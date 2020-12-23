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
% DateTime   : Thu Dec  3 12:03:06 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  176 (1444 expanded)
%              Number of clauses        :  104 ( 403 expanded)
%              Number of leaves         :   19 ( 386 expanded)
%              Depth                    :   22
%              Number of atoms          :  715 (12420 expanded)
%              Number of equality atoms :  362 (4615 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f7,axiom,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40])).

fof(f76,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

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

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1243,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_406,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_10,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_414,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_406,c_10])).

cnf(c_1213,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1471,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2043,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1213,c_36,c_34,c_33,c_31,c_414,c_1471])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_1224,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4066,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1224])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4211,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4066,c_37,c_38,c_39])).

cnf(c_4212,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4211])).

cnf(c_4215,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_4212])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_689,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_718,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_690,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1340,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_1341,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_4313,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_40,c_41,c_42,c_27,c_718,c_1341])).

cnf(c_4317,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_4313])).

cnf(c_1220,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1229,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3084,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1229])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1237,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2501,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1220,c_1237])).

cnf(c_3087,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3084,c_2501])).

cnf(c_3334,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3087,c_41,c_27,c_718,c_1341])).

cnf(c_1218,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1240,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3005,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1240])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1355,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1610,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1355])).

cnf(c_1611,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1610])).

cnf(c_3160,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3005,c_42,c_1611])).

cnf(c_3336,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3334,c_3160])).

cnf(c_4345,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_4317,c_3336])).

cnf(c_1217,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1226,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3608,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1226])).

cnf(c_3728,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3608,c_40])).

cnf(c_3729,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3728])).

cnf(c_3737,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_3729])).

cnf(c_3738,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3737,c_2043])).

cnf(c_4032,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3738,c_37])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1239,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4075,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4032,c_1239])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1236,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2339,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1217,c_1236])).

cnf(c_2340,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2339,c_30])).

cnf(c_2338,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1220,c_1236])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_418,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_419,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_505,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_419])).

cnf(c_1212,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_1687,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1212])).

cnf(c_2050,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1687,c_37,c_38,c_39,c_40,c_41,c_42])).

cnf(c_2341,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2338,c_2050])).

cnf(c_4076,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4075,c_2340,c_2341,c_3334])).

cnf(c_4077,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4076])).

cnf(c_2053,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2054,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2053])).

cnf(c_5271,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4077,c_37,c_39,c_40,c_42,c_1611,c_2054,c_4317])).

cnf(c_5977,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_4345,c_4345,c_5271])).

cnf(c_5985,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5977,c_1239])).

cnf(c_3085,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1229])).

cnf(c_2502,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1217,c_1237])).

cnf(c_3086,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3085,c_2502])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1314,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_1315,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_3228,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3086,c_38,c_26,c_718,c_1315])).

cnf(c_5986,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5985,c_2340,c_2341,c_3228])).

cnf(c_5987,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5986])).

cnf(c_25,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5987,c_2054,c_1611,c_25,c_44,c_42,c_40,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/0.99  
% 3.60/0.99  ------  iProver source info
% 3.60/0.99  
% 3.60/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.60/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/0.99  git: non_committed_changes: false
% 3.60/0.99  git: last_make_outside_of_git: false
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options
% 3.60/0.99  
% 3.60/0.99  --out_options                           all
% 3.60/0.99  --tptp_safe_out                         true
% 3.60/0.99  --problem_path                          ""
% 3.60/0.99  --include_path                          ""
% 3.60/0.99  --clausifier                            res/vclausify_rel
% 3.60/0.99  --clausifier_options                    ""
% 3.60/0.99  --stdin                                 false
% 3.60/0.99  --stats_out                             all
% 3.60/0.99  
% 3.60/0.99  ------ General Options
% 3.60/0.99  
% 3.60/0.99  --fof                                   false
% 3.60/0.99  --time_out_real                         305.
% 3.60/0.99  --time_out_virtual                      -1.
% 3.60/0.99  --symbol_type_check                     false
% 3.60/0.99  --clausify_out                          false
% 3.60/0.99  --sig_cnt_out                           false
% 3.60/0.99  --trig_cnt_out                          false
% 3.60/0.99  --trig_cnt_out_tolerance                1.
% 3.60/0.99  --trig_cnt_out_sk_spl                   false
% 3.60/0.99  --abstr_cl_out                          false
% 3.60/0.99  
% 3.60/0.99  ------ Global Options
% 3.60/0.99  
% 3.60/0.99  --schedule                              default
% 3.60/0.99  --add_important_lit                     false
% 3.60/0.99  --prop_solver_per_cl                    1000
% 3.60/0.99  --min_unsat_core                        false
% 3.60/0.99  --soft_assumptions                      false
% 3.60/0.99  --soft_lemma_size                       3
% 3.60/0.99  --prop_impl_unit_size                   0
% 3.60/0.99  --prop_impl_unit                        []
% 3.60/0.99  --share_sel_clauses                     true
% 3.60/0.99  --reset_solvers                         false
% 3.60/0.99  --bc_imp_inh                            [conj_cone]
% 3.60/0.99  --conj_cone_tolerance                   3.
% 3.60/0.99  --extra_neg_conj                        none
% 3.60/0.99  --large_theory_mode                     true
% 3.60/0.99  --prolific_symb_bound                   200
% 3.60/0.99  --lt_threshold                          2000
% 3.60/0.99  --clause_weak_htbl                      true
% 3.60/0.99  --gc_record_bc_elim                     false
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing Options
% 3.60/0.99  
% 3.60/0.99  --preprocessing_flag                    true
% 3.60/0.99  --time_out_prep_mult                    0.1
% 3.60/0.99  --splitting_mode                        input
% 3.60/0.99  --splitting_grd                         true
% 3.60/0.99  --splitting_cvd                         false
% 3.60/0.99  --splitting_cvd_svl                     false
% 3.60/0.99  --splitting_nvd                         32
% 3.60/0.99  --sub_typing                            true
% 3.60/0.99  --prep_gs_sim                           true
% 3.60/0.99  --prep_unflatten                        true
% 3.60/0.99  --prep_res_sim                          true
% 3.60/0.99  --prep_upred                            true
% 3.60/0.99  --prep_sem_filter                       exhaustive
% 3.60/0.99  --prep_sem_filter_out                   false
% 3.60/0.99  --pred_elim                             true
% 3.60/0.99  --res_sim_input                         true
% 3.60/0.99  --eq_ax_congr_red                       true
% 3.60/0.99  --pure_diseq_elim                       true
% 3.60/0.99  --brand_transform                       false
% 3.60/0.99  --non_eq_to_eq                          false
% 3.60/0.99  --prep_def_merge                        true
% 3.60/0.99  --prep_def_merge_prop_impl              false
% 3.60/0.99  --prep_def_merge_mbd                    true
% 3.60/0.99  --prep_def_merge_tr_red                 false
% 3.60/0.99  --prep_def_merge_tr_cl                  false
% 3.60/0.99  --smt_preprocessing                     true
% 3.60/0.99  --smt_ac_axioms                         fast
% 3.60/0.99  --preprocessed_out                      false
% 3.60/0.99  --preprocessed_stats                    false
% 3.60/0.99  
% 3.60/0.99  ------ Abstraction refinement Options
% 3.60/0.99  
% 3.60/0.99  --abstr_ref                             []
% 3.60/0.99  --abstr_ref_prep                        false
% 3.60/0.99  --abstr_ref_until_sat                   false
% 3.60/0.99  --abstr_ref_sig_restrict                funpre
% 3.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/0.99  --abstr_ref_under                       []
% 3.60/0.99  
% 3.60/0.99  ------ SAT Options
% 3.60/0.99  
% 3.60/0.99  --sat_mode                              false
% 3.60/0.99  --sat_fm_restart_options                ""
% 3.60/0.99  --sat_gr_def                            false
% 3.60/0.99  --sat_epr_types                         true
% 3.60/0.99  --sat_non_cyclic_types                  false
% 3.60/0.99  --sat_finite_models                     false
% 3.60/0.99  --sat_fm_lemmas                         false
% 3.60/0.99  --sat_fm_prep                           false
% 3.60/0.99  --sat_fm_uc_incr                        true
% 3.60/0.99  --sat_out_model                         small
% 3.60/0.99  --sat_out_clauses                       false
% 3.60/0.99  
% 3.60/0.99  ------ QBF Options
% 3.60/0.99  
% 3.60/0.99  --qbf_mode                              false
% 3.60/0.99  --qbf_elim_univ                         false
% 3.60/0.99  --qbf_dom_inst                          none
% 3.60/0.99  --qbf_dom_pre_inst                      false
% 3.60/0.99  --qbf_sk_in                             false
% 3.60/0.99  --qbf_pred_elim                         true
% 3.60/0.99  --qbf_split                             512
% 3.60/0.99  
% 3.60/0.99  ------ BMC1 Options
% 3.60/0.99  
% 3.60/0.99  --bmc1_incremental                      false
% 3.60/0.99  --bmc1_axioms                           reachable_all
% 3.60/0.99  --bmc1_min_bound                        0
% 3.60/0.99  --bmc1_max_bound                        -1
% 3.60/0.99  --bmc1_max_bound_default                -1
% 3.60/0.99  --bmc1_symbol_reachability              true
% 3.60/0.99  --bmc1_property_lemmas                  false
% 3.60/0.99  --bmc1_k_induction                      false
% 3.60/0.99  --bmc1_non_equiv_states                 false
% 3.60/0.99  --bmc1_deadlock                         false
% 3.60/0.99  --bmc1_ucm                              false
% 3.60/0.99  --bmc1_add_unsat_core                   none
% 3.60/0.99  --bmc1_unsat_core_children              false
% 3.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/0.99  --bmc1_out_stat                         full
% 3.60/0.99  --bmc1_ground_init                      false
% 3.60/0.99  --bmc1_pre_inst_next_state              false
% 3.60/0.99  --bmc1_pre_inst_state                   false
% 3.60/0.99  --bmc1_pre_inst_reach_state             false
% 3.60/0.99  --bmc1_out_unsat_core                   false
% 3.60/0.99  --bmc1_aig_witness_out                  false
% 3.60/0.99  --bmc1_verbose                          false
% 3.60/0.99  --bmc1_dump_clauses_tptp                false
% 3.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.60/0.99  --bmc1_dump_file                        -
% 3.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.60/0.99  --bmc1_ucm_extend_mode                  1
% 3.60/0.99  --bmc1_ucm_init_mode                    2
% 3.60/0.99  --bmc1_ucm_cone_mode                    none
% 3.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.60/0.99  --bmc1_ucm_relax_model                  4
% 3.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/0.99  --bmc1_ucm_layered_model                none
% 3.60/0.99  --bmc1_ucm_max_lemma_size               10
% 3.60/0.99  
% 3.60/0.99  ------ AIG Options
% 3.60/0.99  
% 3.60/0.99  --aig_mode                              false
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation Options
% 3.60/0.99  
% 3.60/0.99  --instantiation_flag                    true
% 3.60/0.99  --inst_sos_flag                         true
% 3.60/0.99  --inst_sos_phase                        true
% 3.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel_side                     num_symb
% 3.60/0.99  --inst_solver_per_active                1400
% 3.60/0.99  --inst_solver_calls_frac                1.
% 3.60/0.99  --inst_passive_queue_type               priority_queues
% 3.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/0.99  --inst_passive_queues_freq              [25;2]
% 3.60/0.99  --inst_dismatching                      true
% 3.60/0.99  --inst_eager_unprocessed_to_passive     true
% 3.60/0.99  --inst_prop_sim_given                   true
% 3.60/0.99  --inst_prop_sim_new                     false
% 3.60/0.99  --inst_subs_new                         false
% 3.60/0.99  --inst_eq_res_simp                      false
% 3.60/0.99  --inst_subs_given                       false
% 3.60/0.99  --inst_orphan_elimination               true
% 3.60/0.99  --inst_learning_loop_flag               true
% 3.60/0.99  --inst_learning_start                   3000
% 3.60/0.99  --inst_learning_factor                  2
% 3.60/0.99  --inst_start_prop_sim_after_learn       3
% 3.60/0.99  --inst_sel_renew                        solver
% 3.60/0.99  --inst_lit_activity_flag                true
% 3.60/0.99  --inst_restr_to_given                   false
% 3.60/0.99  --inst_activity_threshold               500
% 3.60/0.99  --inst_out_proof                        true
% 3.60/0.99  
% 3.60/0.99  ------ Resolution Options
% 3.60/0.99  
% 3.60/0.99  --resolution_flag                       true
% 3.60/0.99  --res_lit_sel                           adaptive
% 3.60/0.99  --res_lit_sel_side                      none
% 3.60/0.99  --res_ordering                          kbo
% 3.60/0.99  --res_to_prop_solver                    active
% 3.60/0.99  --res_prop_simpl_new                    false
% 3.60/0.99  --res_prop_simpl_given                  true
% 3.60/0.99  --res_passive_queue_type                priority_queues
% 3.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/0.99  --res_passive_queues_freq               [15;5]
% 3.60/0.99  --res_forward_subs                      full
% 3.60/0.99  --res_backward_subs                     full
% 3.60/0.99  --res_forward_subs_resolution           true
% 3.60/0.99  --res_backward_subs_resolution          true
% 3.60/0.99  --res_orphan_elimination                true
% 3.60/0.99  --res_time_limit                        2.
% 3.60/0.99  --res_out_proof                         true
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Options
% 3.60/0.99  
% 3.60/0.99  --superposition_flag                    true
% 3.60/0.99  --sup_passive_queue_type                priority_queues
% 3.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.60/0.99  --demod_completeness_check              fast
% 3.60/0.99  --demod_use_ground                      true
% 3.60/0.99  --sup_to_prop_solver                    passive
% 3.60/0.99  --sup_prop_simpl_new                    true
% 3.60/0.99  --sup_prop_simpl_given                  true
% 3.60/0.99  --sup_fun_splitting                     true
% 3.60/0.99  --sup_smt_interval                      50000
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Simplification Setup
% 3.60/0.99  
% 3.60/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.60/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.60/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.60/0.99  --sup_immed_triv                        [TrivRules]
% 3.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_bw_main                     []
% 3.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_input_bw                          []
% 3.60/0.99  
% 3.60/0.99  ------ Combination Options
% 3.60/0.99  
% 3.60/0.99  --comb_res_mult                         3
% 3.60/0.99  --comb_sup_mult                         2
% 3.60/0.99  --comb_inst_mult                        10
% 3.60/0.99  
% 3.60/0.99  ------ Debug Options
% 3.60/0.99  
% 3.60/0.99  --dbg_backtrace                         false
% 3.60/0.99  --dbg_dump_prop_clauses                 false
% 3.60/0.99  --dbg_dump_prop_clauses_file            -
% 3.60/0.99  --dbg_out_stat                          false
% 3.60/0.99  ------ Parsing...
% 3.60/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/0.99  ------ Proving...
% 3.60/0.99  ------ Problem Properties 
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  clauses                                 36
% 3.60/0.99  conjectures                             11
% 3.60/0.99  EPR                                     7
% 3.60/0.99  Horn                                    30
% 3.60/0.99  unary                                   14
% 3.60/0.99  binary                                  4
% 3.60/0.99  lits                                    128
% 3.60/0.99  lits eq                                 32
% 3.60/0.99  fd_pure                                 0
% 3.60/0.99  fd_pseudo                               0
% 3.60/0.99  fd_cond                                 5
% 3.60/0.99  fd_pseudo_cond                          1
% 3.60/0.99  AC symbols                              0
% 3.60/0.99  
% 3.60/0.99  ------ Schedule dynamic 5 is on 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  Current options:
% 3.60/0.99  ------ 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options
% 3.60/0.99  
% 3.60/0.99  --out_options                           all
% 3.60/0.99  --tptp_safe_out                         true
% 3.60/0.99  --problem_path                          ""
% 3.60/0.99  --include_path                          ""
% 3.60/0.99  --clausifier                            res/vclausify_rel
% 3.60/0.99  --clausifier_options                    ""
% 3.60/0.99  --stdin                                 false
% 3.60/0.99  --stats_out                             all
% 3.60/0.99  
% 3.60/0.99  ------ General Options
% 3.60/0.99  
% 3.60/0.99  --fof                                   false
% 3.60/0.99  --time_out_real                         305.
% 3.60/0.99  --time_out_virtual                      -1.
% 3.60/0.99  --symbol_type_check                     false
% 3.60/0.99  --clausify_out                          false
% 3.60/0.99  --sig_cnt_out                           false
% 3.60/0.99  --trig_cnt_out                          false
% 3.60/0.99  --trig_cnt_out_tolerance                1.
% 3.60/0.99  --trig_cnt_out_sk_spl                   false
% 3.60/0.99  --abstr_cl_out                          false
% 3.60/0.99  
% 3.60/0.99  ------ Global Options
% 3.60/0.99  
% 3.60/0.99  --schedule                              default
% 3.60/0.99  --add_important_lit                     false
% 3.60/0.99  --prop_solver_per_cl                    1000
% 3.60/0.99  --min_unsat_core                        false
% 3.60/0.99  --soft_assumptions                      false
% 3.60/0.99  --soft_lemma_size                       3
% 3.60/0.99  --prop_impl_unit_size                   0
% 3.60/0.99  --prop_impl_unit                        []
% 3.60/0.99  --share_sel_clauses                     true
% 3.60/0.99  --reset_solvers                         false
% 3.60/0.99  --bc_imp_inh                            [conj_cone]
% 3.60/0.99  --conj_cone_tolerance                   3.
% 3.60/0.99  --extra_neg_conj                        none
% 3.60/0.99  --large_theory_mode                     true
% 3.60/0.99  --prolific_symb_bound                   200
% 3.60/0.99  --lt_threshold                          2000
% 3.60/0.99  --clause_weak_htbl                      true
% 3.60/0.99  --gc_record_bc_elim                     false
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing Options
% 3.60/0.99  
% 3.60/0.99  --preprocessing_flag                    true
% 3.60/0.99  --time_out_prep_mult                    0.1
% 3.60/0.99  --splitting_mode                        input
% 3.60/0.99  --splitting_grd                         true
% 3.60/0.99  --splitting_cvd                         false
% 3.60/0.99  --splitting_cvd_svl                     false
% 3.60/0.99  --splitting_nvd                         32
% 3.60/0.99  --sub_typing                            true
% 3.60/0.99  --prep_gs_sim                           true
% 3.60/0.99  --prep_unflatten                        true
% 3.60/0.99  --prep_res_sim                          true
% 3.60/0.99  --prep_upred                            true
% 3.60/0.99  --prep_sem_filter                       exhaustive
% 3.60/0.99  --prep_sem_filter_out                   false
% 3.60/0.99  --pred_elim                             true
% 3.60/0.99  --res_sim_input                         true
% 3.60/0.99  --eq_ax_congr_red                       true
% 3.60/0.99  --pure_diseq_elim                       true
% 3.60/0.99  --brand_transform                       false
% 3.60/0.99  --non_eq_to_eq                          false
% 3.60/0.99  --prep_def_merge                        true
% 3.60/0.99  --prep_def_merge_prop_impl              false
% 3.60/0.99  --prep_def_merge_mbd                    true
% 3.60/0.99  --prep_def_merge_tr_red                 false
% 3.60/0.99  --prep_def_merge_tr_cl                  false
% 3.60/0.99  --smt_preprocessing                     true
% 3.60/0.99  --smt_ac_axioms                         fast
% 3.60/0.99  --preprocessed_out                      false
% 3.60/0.99  --preprocessed_stats                    false
% 3.60/0.99  
% 3.60/0.99  ------ Abstraction refinement Options
% 3.60/0.99  
% 3.60/0.99  --abstr_ref                             []
% 3.60/0.99  --abstr_ref_prep                        false
% 3.60/0.99  --abstr_ref_until_sat                   false
% 3.60/0.99  --abstr_ref_sig_restrict                funpre
% 3.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/0.99  --abstr_ref_under                       []
% 3.60/0.99  
% 3.60/0.99  ------ SAT Options
% 3.60/0.99  
% 3.60/0.99  --sat_mode                              false
% 3.60/0.99  --sat_fm_restart_options                ""
% 3.60/0.99  --sat_gr_def                            false
% 3.60/0.99  --sat_epr_types                         true
% 3.60/0.99  --sat_non_cyclic_types                  false
% 3.60/0.99  --sat_finite_models                     false
% 3.60/0.99  --sat_fm_lemmas                         false
% 3.60/0.99  --sat_fm_prep                           false
% 3.60/0.99  --sat_fm_uc_incr                        true
% 3.60/0.99  --sat_out_model                         small
% 3.60/0.99  --sat_out_clauses                       false
% 3.60/0.99  
% 3.60/0.99  ------ QBF Options
% 3.60/0.99  
% 3.60/0.99  --qbf_mode                              false
% 3.60/0.99  --qbf_elim_univ                         false
% 3.60/0.99  --qbf_dom_inst                          none
% 3.60/0.99  --qbf_dom_pre_inst                      false
% 3.60/0.99  --qbf_sk_in                             false
% 3.60/0.99  --qbf_pred_elim                         true
% 3.60/0.99  --qbf_split                             512
% 3.60/0.99  
% 3.60/0.99  ------ BMC1 Options
% 3.60/0.99  
% 3.60/0.99  --bmc1_incremental                      false
% 3.60/0.99  --bmc1_axioms                           reachable_all
% 3.60/0.99  --bmc1_min_bound                        0
% 3.60/0.99  --bmc1_max_bound                        -1
% 3.60/0.99  --bmc1_max_bound_default                -1
% 3.60/0.99  --bmc1_symbol_reachability              true
% 3.60/0.99  --bmc1_property_lemmas                  false
% 3.60/0.99  --bmc1_k_induction                      false
% 3.60/0.99  --bmc1_non_equiv_states                 false
% 3.60/0.99  --bmc1_deadlock                         false
% 3.60/0.99  --bmc1_ucm                              false
% 3.60/0.99  --bmc1_add_unsat_core                   none
% 3.60/0.99  --bmc1_unsat_core_children              false
% 3.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/0.99  --bmc1_out_stat                         full
% 3.60/0.99  --bmc1_ground_init                      false
% 3.60/0.99  --bmc1_pre_inst_next_state              false
% 3.60/0.99  --bmc1_pre_inst_state                   false
% 3.60/0.99  --bmc1_pre_inst_reach_state             false
% 3.60/0.99  --bmc1_out_unsat_core                   false
% 3.60/0.99  --bmc1_aig_witness_out                  false
% 3.60/0.99  --bmc1_verbose                          false
% 3.60/0.99  --bmc1_dump_clauses_tptp                false
% 3.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.60/0.99  --bmc1_dump_file                        -
% 3.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.60/0.99  --bmc1_ucm_extend_mode                  1
% 3.60/0.99  --bmc1_ucm_init_mode                    2
% 3.60/0.99  --bmc1_ucm_cone_mode                    none
% 3.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.60/0.99  --bmc1_ucm_relax_model                  4
% 3.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/0.99  --bmc1_ucm_layered_model                none
% 3.60/0.99  --bmc1_ucm_max_lemma_size               10
% 3.60/0.99  
% 3.60/0.99  ------ AIG Options
% 3.60/0.99  
% 3.60/0.99  --aig_mode                              false
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation Options
% 3.60/0.99  
% 3.60/0.99  --instantiation_flag                    true
% 3.60/0.99  --inst_sos_flag                         true
% 3.60/0.99  --inst_sos_phase                        true
% 3.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel_side                     none
% 3.60/0.99  --inst_solver_per_active                1400
% 3.60/0.99  --inst_solver_calls_frac                1.
% 3.60/0.99  --inst_passive_queue_type               priority_queues
% 3.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/0.99  --inst_passive_queues_freq              [25;2]
% 3.60/0.99  --inst_dismatching                      true
% 3.60/0.99  --inst_eager_unprocessed_to_passive     true
% 3.60/0.99  --inst_prop_sim_given                   true
% 3.60/0.99  --inst_prop_sim_new                     false
% 3.60/0.99  --inst_subs_new                         false
% 3.60/0.99  --inst_eq_res_simp                      false
% 3.60/0.99  --inst_subs_given                       false
% 3.60/0.99  --inst_orphan_elimination               true
% 3.60/0.99  --inst_learning_loop_flag               true
% 3.60/0.99  --inst_learning_start                   3000
% 3.60/0.99  --inst_learning_factor                  2
% 3.60/0.99  --inst_start_prop_sim_after_learn       3
% 3.60/0.99  --inst_sel_renew                        solver
% 3.60/0.99  --inst_lit_activity_flag                true
% 3.60/0.99  --inst_restr_to_given                   false
% 3.60/0.99  --inst_activity_threshold               500
% 3.60/0.99  --inst_out_proof                        true
% 3.60/0.99  
% 3.60/0.99  ------ Resolution Options
% 3.60/0.99  
% 3.60/0.99  --resolution_flag                       false
% 3.60/0.99  --res_lit_sel                           adaptive
% 3.60/0.99  --res_lit_sel_side                      none
% 3.60/0.99  --res_ordering                          kbo
% 3.60/0.99  --res_to_prop_solver                    active
% 3.60/0.99  --res_prop_simpl_new                    false
% 3.60/0.99  --res_prop_simpl_given                  true
% 3.60/0.99  --res_passive_queue_type                priority_queues
% 3.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/0.99  --res_passive_queues_freq               [15;5]
% 3.60/0.99  --res_forward_subs                      full
% 3.60/0.99  --res_backward_subs                     full
% 3.60/0.99  --res_forward_subs_resolution           true
% 3.60/0.99  --res_backward_subs_resolution          true
% 3.60/0.99  --res_orphan_elimination                true
% 3.60/0.99  --res_time_limit                        2.
% 3.60/0.99  --res_out_proof                         true
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Options
% 3.60/0.99  
% 3.60/0.99  --superposition_flag                    true
% 3.60/0.99  --sup_passive_queue_type                priority_queues
% 3.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.60/0.99  --demod_completeness_check              fast
% 3.60/0.99  --demod_use_ground                      true
% 3.60/0.99  --sup_to_prop_solver                    passive
% 3.60/0.99  --sup_prop_simpl_new                    true
% 3.60/0.99  --sup_prop_simpl_given                  true
% 3.60/0.99  --sup_fun_splitting                     true
% 3.60/0.99  --sup_smt_interval                      50000
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Simplification Setup
% 3.60/0.99  
% 3.60/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.60/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.60/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.60/0.99  --sup_immed_triv                        [TrivRules]
% 3.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_bw_main                     []
% 3.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_input_bw                          []
% 3.60/0.99  
% 3.60/0.99  ------ Combination Options
% 3.60/0.99  
% 3.60/0.99  --comb_res_mult                         3
% 3.60/0.99  --comb_sup_mult                         2
% 3.60/0.99  --comb_inst_mult                        10
% 3.60/0.99  
% 3.60/0.99  ------ Debug Options
% 3.60/0.99  
% 3.60/0.99  --dbg_backtrace                         false
% 3.60/0.99  --dbg_dump_prop_clauses                 false
% 3.60/0.99  --dbg_dump_prop_clauses_file            -
% 3.60/0.99  --dbg_out_stat                          false
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ Proving...
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS status Theorem for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  fof(f1,axiom,(
% 3.60/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f44,plain,(
% 3.60/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f1])).
% 3.60/0.99  
% 3.60/0.99  fof(f12,axiom,(
% 3.60/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f63,plain,(
% 3.60/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f12])).
% 3.60/0.99  
% 3.60/0.99  fof(f81,plain,(
% 3.60/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.60/0.99    inference(definition_unfolding,[],[f44,f63])).
% 3.60/0.99  
% 3.60/0.99  fof(f7,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f24,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.60/0.99    inference(ennf_transformation,[],[f7])).
% 3.60/0.99  
% 3.60/0.99  fof(f25,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(flattening,[],[f24])).
% 3.60/0.99  
% 3.60/0.99  fof(f38,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(nnf_transformation,[],[f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f51,plain,(
% 3.60/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f38])).
% 3.60/0.99  
% 3.60/0.99  fof(f15,conjecture,(
% 3.60/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f16,negated_conjecture,(
% 3.60/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.60/0.99    inference(negated_conjecture,[],[f15])).
% 3.60/0.99  
% 3.60/0.99  fof(f36,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.60/0.99    inference(ennf_transformation,[],[f16])).
% 3.60/0.99  
% 3.60/0.99  fof(f37,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.60/0.99    inference(flattening,[],[f36])).
% 3.60/0.99  
% 3.60/0.99  fof(f41,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.60/0.99    introduced(choice_axiom,[])).
% 3.60/0.99  
% 3.60/0.99  fof(f40,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.60/0.99    introduced(choice_axiom,[])).
% 3.60/0.99  
% 3.60/0.99  fof(f42,plain,(
% 3.60/0.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40])).
% 3.60/0.99  
% 3.60/0.99  fof(f76,plain,(
% 3.60/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f8,axiom,(
% 3.60/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f53,plain,(
% 3.60/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f8])).
% 3.60/0.99  
% 3.60/0.99  fof(f86,plain,(
% 3.60/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.60/0.99    inference(definition_unfolding,[],[f53,f63])).
% 3.60/0.99  
% 3.60/0.99  fof(f69,plain,(
% 3.60/0.99    v1_funct_1(sK2)),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f71,plain,(
% 3.60/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f72,plain,(
% 3.60/0.99    v1_funct_1(sK3)),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f74,plain,(
% 3.60/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f10,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f28,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.60/0.99    inference(ennf_transformation,[],[f10])).
% 3.60/0.99  
% 3.60/0.99  fof(f29,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.60/0.99    inference(flattening,[],[f28])).
% 3.60/0.99  
% 3.60/0.99  fof(f61,plain,(
% 3.60/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f29])).
% 3.60/0.99  
% 3.60/0.99  fof(f75,plain,(
% 3.60/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f14,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f34,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.60/0.99    inference(ennf_transformation,[],[f14])).
% 3.60/0.99  
% 3.60/0.99  fof(f35,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.60/0.99    inference(flattening,[],[f34])).
% 3.60/0.99  
% 3.60/0.99  fof(f67,plain,(
% 3.60/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f35])).
% 3.60/0.99  
% 3.60/0.99  fof(f70,plain,(
% 3.60/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f73,plain,(
% 3.60/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f78,plain,(
% 3.60/0.99    k1_xboole_0 != sK0),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f9,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f26,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f9])).
% 3.60/0.99  
% 3.60/0.99  fof(f27,plain,(
% 3.60/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(flattening,[],[f26])).
% 3.60/0.99  
% 3.60/0.99  fof(f39,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(nnf_transformation,[],[f27])).
% 3.60/0.99  
% 3.60/0.99  fof(f54,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f5,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f22,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f5])).
% 3.60/0.99  
% 3.60/0.99  fof(f49,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f22])).
% 3.60/0.99  
% 3.60/0.99  fof(f2,axiom,(
% 3.60/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f17,plain,(
% 3.60/0.99    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.60/0.99    inference(ennf_transformation,[],[f2])).
% 3.60/0.99  
% 3.60/0.99  fof(f18,plain,(
% 3.60/0.99    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.60/0.99    inference(flattening,[],[f17])).
% 3.60/0.99  
% 3.60/0.99  fof(f45,plain,(
% 3.60/0.99    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f18])).
% 3.60/0.99  
% 3.60/0.99  fof(f84,plain,(
% 3.60/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(definition_unfolding,[],[f45,f63])).
% 3.60/0.99  
% 3.60/0.99  fof(f4,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f21,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f4])).
% 3.60/0.99  
% 3.60/0.99  fof(f48,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f21])).
% 3.60/0.99  
% 3.60/0.99  fof(f11,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f30,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.60/0.99    inference(ennf_transformation,[],[f11])).
% 3.60/0.99  
% 3.60/0.99  fof(f31,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.60/0.99    inference(flattening,[],[f30])).
% 3.60/0.99  
% 3.60/0.99  fof(f62,plain,(
% 3.60/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f31])).
% 3.60/0.99  
% 3.60/0.99  fof(f3,axiom,(
% 3.60/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f19,plain,(
% 3.60/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.60/0.99    inference(ennf_transformation,[],[f3])).
% 3.60/0.99  
% 3.60/0.99  fof(f20,plain,(
% 3.60/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.60/0.99    inference(flattening,[],[f19])).
% 3.60/0.99  
% 3.60/0.99  fof(f47,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f20])).
% 3.60/0.99  
% 3.60/0.99  fof(f85,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(definition_unfolding,[],[f47,f63])).
% 3.60/0.99  
% 3.60/0.99  fof(f6,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f23,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f6])).
% 3.60/0.99  
% 3.60/0.99  fof(f50,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f23])).
% 3.60/0.99  
% 3.60/0.99  fof(f13,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f32,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.60/0.99    inference(ennf_transformation,[],[f13])).
% 3.60/0.99  
% 3.60/0.99  fof(f33,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.60/0.99    inference(flattening,[],[f32])).
% 3.60/0.99  
% 3.60/0.99  fof(f64,plain,(
% 3.60/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f33])).
% 3.60/0.99  
% 3.60/0.99  fof(f79,plain,(
% 3.60/0.99    k1_xboole_0 != sK1),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f80,plain,(
% 3.60/0.99    k2_funct_1(sK2) != sK3),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f77,plain,(
% 3.60/0.99    v2_funct_1(sK2)),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  cnf(c_0,plain,
% 3.60/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1243,plain,
% 3.60/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_9,plain,
% 3.60/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.60/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | X3 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_29,negated_conjecture,
% 3.60/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_405,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | X3 = X0
% 3.60/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.60/0.99      | k6_partfun1(sK0) != X3
% 3.60/0.99      | sK0 != X2
% 3.60/0.99      | sK0 != X1 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_406,plain,
% 3.60/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.60/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.60/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_405]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_10,plain,
% 3.60/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_414,plain,
% 3.60/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.60/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.60/0.99      inference(forward_subsumption_resolution,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_406,c_10]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1213,plain,
% 3.60/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.60/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_36,negated_conjecture,
% 3.60/0.99      ( v1_funct_1(sK2) ),
% 3.60/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_34,negated_conjecture,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_33,negated_conjecture,
% 3.60/0.99      ( v1_funct_1(sK3) ),
% 3.60/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_31,negated_conjecture,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_17,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.60/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X3) ),
% 3.60/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1471,plain,
% 3.60/0.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.60/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | ~ v1_funct_1(sK3)
% 3.60/0.99      | ~ v1_funct_1(sK2) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2043,plain,
% 3.60/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_1213,c_36,c_34,c_33,c_31,c_414,c_1471]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_30,negated_conjecture,
% 3.60/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.60/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_22,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ v1_funct_2(X3,X4,X1)
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X3)
% 3.60/0.99      | v2_funct_1(X0)
% 3.60/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.60/0.99      | k2_relset_1(X4,X1,X3) != X1
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1224,plain,
% 3.60/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.60/0.99      | k1_xboole_0 = X3
% 3.60/0.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.60/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.60/0.99      | v1_funct_1(X4) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top
% 3.60/0.99      | v2_funct_1(X4) = iProver_top
% 3.60/0.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4066,plain,
% 3.60/0.99      ( k1_xboole_0 = X0
% 3.60/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.60/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X1) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top
% 3.60/0.99      | v2_funct_1(X1) = iProver_top
% 3.60/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_30,c_1224]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_37,plain,
% 3.60/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_35,negated_conjecture,
% 3.60/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.60/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_38,plain,
% 3.60/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_39,plain,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4211,plain,
% 3.60/0.99      ( v1_funct_1(X1) != iProver_top
% 3.60/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.60/0.99      | k1_xboole_0 = X0
% 3.60/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.60/0.99      | v2_funct_1(X1) = iProver_top
% 3.60/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4066,c_37,c_38,c_39]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4212,plain,
% 3.60/0.99      ( k1_xboole_0 = X0
% 3.60/0.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.60/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.60/0.99      | v1_funct_1(X1) != iProver_top
% 3.60/0.99      | v2_funct_1(X1) = iProver_top
% 3.60/0.99      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_4211]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4215,plain,
% 3.60/0.99      ( sK0 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.60/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.60/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_2043,c_4212]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_40,plain,
% 3.60/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_32,negated_conjecture,
% 3.60/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_41,plain,
% 3.60/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_42,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_27,negated_conjecture,
% 3.60/0.99      ( k1_xboole_0 != sK0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_689,plain,( X0 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_718,plain,
% 3.60/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_689]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_690,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1340,plain,
% 3.60/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_690]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1341,plain,
% 3.60/0.99      ( sK0 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = sK0
% 3.60/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_1340]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4313,plain,
% 3.60/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.60/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4215,c_40,c_41,c_42,c_27,c_718,c_1341]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4317,plain,
% 3.60/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1243,c_4313]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1220,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_16,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1229,plain,
% 3.60/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.60/0.99      | k1_xboole_0 = X1
% 3.60/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3084,plain,
% 3.60/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.60/0.99      | sK0 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1220,c_1229]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_6,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1237,plain,
% 3.60/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2501,plain,
% 3.60/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1220,c_1237]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3087,plain,
% 3.60/0.99      ( k1_relat_1(sK3) = sK1
% 3.60/0.99      | sK0 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_3084,c_2501]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3334,plain,
% 3.60/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3087,c_41,c_27,c_718,c_1341]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1218,plain,
% 3.60/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3,plain,
% 3.60/0.99      ( ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1240,plain,
% 3.60/0.99      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.60/0.99      | v1_funct_1(X0) != iProver_top
% 3.60/0.99      | v1_relat_1(X0) != iProver_top
% 3.60/0.99      | v2_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3005,plain,
% 3.60/0.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1218,c_1240]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | v1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1355,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | v1_relat_1(sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1610,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.60/0.99      | v1_relat_1(sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_1355]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1611,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_1610]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3160,plain,
% 3.60/0.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 3.60/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3005,c_42,c_1611]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3336,plain,
% 3.60/0.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.60/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_3334,c_3160]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4345,plain,
% 3.60/0.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_4317,c_3336]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1217,plain,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_19,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X3)
% 3.60/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1226,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.60/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.60/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X5) != iProver_top
% 3.60/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3608,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1220,c_1226]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3728,plain,
% 3.60/0.99      ( v1_funct_1(X2) != iProver_top
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3608,c_40]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3729,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_3728]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3737,plain,
% 3.60/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1217,c_3729]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3738,plain,
% 3.60/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_3737,c_2043]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4032,plain,
% 3.60/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3738,c_37]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4,plain,
% 3.60/0.99      ( ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X1)
% 3.60/0.99      | ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_relat_1(X1)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(X1)
% 3.60/0.99      | k2_funct_1(X0) = X1 ),
% 3.60/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1239,plain,
% 3.60/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.60/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.60/0.99      | k2_funct_1(X1) = X0
% 3.60/0.99      | v1_funct_1(X1) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top
% 3.60/0.99      | v1_relat_1(X1) != iProver_top
% 3.60/0.99      | v1_relat_1(X0) != iProver_top
% 3.60/0.99      | v2_funct_1(X1) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4075,plain,
% 3.60/0.99      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.60/0.99      | k2_funct_1(sK3) = sK2
% 3.60/0.99      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_4032,c_1239]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1236,plain,
% 3.60/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2339,plain,
% 3.60/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1217,c_1236]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2340,plain,
% 3.60/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_2339,c_30]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2338,plain,
% 3.60/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1220,c_1236]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_20,plain,
% 3.60/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.60/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.60/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.60/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_1(X2)
% 3.60/0.99      | ~ v1_funct_1(X3)
% 3.60/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_418,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.60/0.99      | ~ v1_funct_1(X3)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.60/0.99      | k2_relset_1(X2,X1,X3) = X1
% 3.60/0.99      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.60/0.99      | sK0 != X1 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_419,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.60/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.60/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.60/0.99      | ~ v1_funct_1(X2)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.60/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 3.60/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_418]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_505,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.60/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.60/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X2)
% 3.60/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.60/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.60/0.99      inference(equality_resolution_simp,[status(thm)],[c_419]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1212,plain,
% 3.60/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.60/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 3.60/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.60/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.60/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top
% 3.60/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1687,plain,
% 3.60/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.60/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(equality_resolution,[status(thm)],[c_1212]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2050,plain,
% 3.60/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_1687,c_37,c_38,c_39,c_40,c_41,c_42]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2341,plain,
% 3.60/0.99      ( k2_relat_1(sK3) = sK0 ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_2338,c_2050]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4076,plain,
% 3.60/0.99      ( k2_funct_1(sK3) = sK2
% 3.60/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.60/0.99      | sK1 != sK1
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(light_normalisation,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4075,c_2340,c_2341,c_3334]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4077,plain,
% 3.60/0.99      ( k2_funct_1(sK3) = sK2
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(equality_resolution_simp,[status(thm)],[c_4076]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2053,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | v1_relat_1(sK2) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2054,plain,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_2053]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5271,plain,
% 3.60/0.99      ( k2_funct_1(sK3) = sK2 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4077,c_37,c_39,c_40,c_42,c_1611,c_2054,c_4317]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5977,plain,
% 3.60/0.99      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_4345,c_4345,c_5271]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5985,plain,
% 3.60/0.99      ( k1_relat_1(sK2) != k2_relat_1(sK3)
% 3.60/0.99      | k2_funct_1(sK2) = sK3
% 3.60/0.99      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_5977,c_1239]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3085,plain,
% 3.60/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 3.60/0.99      | sK1 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1217,c_1229]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2502,plain,
% 3.60/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1217,c_1237]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3086,plain,
% 3.60/0.99      ( k1_relat_1(sK2) = sK0
% 3.60/0.99      | sK1 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_3085,c_2502]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_26,negated_conjecture,
% 3.60/0.99      ( k1_xboole_0 != sK1 ),
% 3.60/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1314,plain,
% 3.60/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_690]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1315,plain,
% 3.60/0.99      ( sK1 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = sK1
% 3.60/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_1314]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3228,plain,
% 3.60/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3086,c_38,c_26,c_718,c_1315]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5986,plain,
% 3.60/0.99      ( k2_funct_1(sK2) = sK3
% 3.60/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 3.60/0.99      | sK0 != sK0
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(light_normalisation,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_5985,c_2340,c_2341,c_3228]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5987,plain,
% 3.60/0.99      ( k2_funct_1(sK2) = sK3
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(equality_resolution_simp,[status(thm)],[c_5986]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_25,negated_conjecture,
% 3.60/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.60/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_28,negated_conjecture,
% 3.60/0.99      ( v2_funct_1(sK2) ),
% 3.60/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_44,plain,
% 3.60/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(contradiction,plain,
% 3.60/0.99      ( $false ),
% 3.60/0.99      inference(minisat,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_5987,c_2054,c_1611,c_25,c_44,c_42,c_40,c_39,c_37]) ).
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  ------                               Statistics
% 3.60/0.99  
% 3.60/0.99  ------ General
% 3.60/0.99  
% 3.60/0.99  abstr_ref_over_cycles:                  0
% 3.60/0.99  abstr_ref_under_cycles:                 0
% 3.60/0.99  gc_basic_clause_elim:                   0
% 3.60/0.99  forced_gc_time:                         0
% 3.60/0.99  parsing_time:                           0.011
% 3.60/0.99  unif_index_cands_time:                  0.
% 3.60/0.99  unif_index_add_time:                    0.
% 3.60/0.99  orderings_time:                         0.
% 3.60/0.99  out_proof_time:                         0.012
% 3.60/0.99  total_time:                             0.277
% 3.60/0.99  num_of_symbols:                         52
% 3.60/0.99  num_of_terms:                           9526
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing
% 3.60/0.99  
% 3.60/0.99  num_of_splits:                          0
% 3.60/0.99  num_of_split_atoms:                     0
% 3.60/0.99  num_of_reused_defs:                     0
% 3.60/0.99  num_eq_ax_congr_red:                    12
% 3.60/0.99  num_of_sem_filtered_clauses:            1
% 3.60/0.99  num_of_subtypes:                        0
% 3.60/0.99  monotx_restored_types:                  0
% 3.60/0.99  sat_num_of_epr_types:                   0
% 3.60/0.99  sat_num_of_non_cyclic_types:            0
% 3.60/0.99  sat_guarded_non_collapsed_types:        0
% 3.60/0.99  num_pure_diseq_elim:                    0
% 3.60/0.99  simp_replaced_by:                       0
% 3.60/0.99  res_preprocessed:                       176
% 3.60/0.99  prep_upred:                             0
% 3.60/0.99  prep_unflattend:                        12
% 3.60/0.99  smt_new_axioms:                         0
% 3.60/0.99  pred_elim_cands:                        5
% 3.60/0.99  pred_elim:                              1
% 3.60/0.99  pred_elim_cl:                           1
% 3.60/0.99  pred_elim_cycles:                       3
% 3.60/0.99  merged_defs:                            0
% 3.60/0.99  merged_defs_ncl:                        0
% 3.60/0.99  bin_hyper_res:                          0
% 3.60/0.99  prep_cycles:                            4
% 3.60/0.99  pred_elim_time:                         0.004
% 3.60/0.99  splitting_time:                         0.
% 3.60/0.99  sem_filter_time:                        0.
% 3.60/0.99  monotx_time:                            0.001
% 3.60/0.99  subtype_inf_time:                       0.
% 3.60/0.99  
% 3.60/0.99  ------ Problem properties
% 3.60/0.99  
% 3.60/0.99  clauses:                                36
% 3.60/0.99  conjectures:                            11
% 3.60/0.99  epr:                                    7
% 3.60/0.99  horn:                                   30
% 3.60/0.99  ground:                                 12
% 3.60/0.99  unary:                                  14
% 3.60/0.99  binary:                                 4
% 3.60/0.99  lits:                                   128
% 3.60/0.99  lits_eq:                                32
% 3.60/0.99  fd_pure:                                0
% 3.60/0.99  fd_pseudo:                              0
% 3.60/0.99  fd_cond:                                5
% 3.60/0.99  fd_pseudo_cond:                         1
% 3.60/0.99  ac_symbols:                             0
% 3.60/0.99  
% 3.60/0.99  ------ Propositional Solver
% 3.60/0.99  
% 3.60/0.99  prop_solver_calls:                      29
% 3.60/0.99  prop_fast_solver_calls:                 1572
% 3.60/0.99  smt_solver_calls:                       0
% 3.60/0.99  smt_fast_solver_calls:                  0
% 3.60/0.99  prop_num_of_clauses:                    2795
% 3.60/0.99  prop_preprocess_simplified:             8050
% 3.60/0.99  prop_fo_subsumed:                       68
% 3.60/0.99  prop_solver_time:                       0.
% 3.60/0.99  smt_solver_time:                        0.
% 3.60/0.99  smt_fast_solver_time:                   0.
% 3.60/0.99  prop_fast_solver_time:                  0.
% 3.60/0.99  prop_unsat_core_time:                   0.
% 3.60/0.99  
% 3.60/0.99  ------ QBF
% 3.60/0.99  
% 3.60/0.99  qbf_q_res:                              0
% 3.60/0.99  qbf_num_tautologies:                    0
% 3.60/0.99  qbf_prep_cycles:                        0
% 3.60/0.99  
% 3.60/0.99  ------ BMC1
% 3.60/0.99  
% 3.60/0.99  bmc1_current_bound:                     -1
% 3.60/0.99  bmc1_last_solved_bound:                 -1
% 3.60/0.99  bmc1_unsat_core_size:                   -1
% 3.60/0.99  bmc1_unsat_core_parents_size:           -1
% 3.60/0.99  bmc1_merge_next_fun:                    0
% 3.60/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation
% 3.60/0.99  
% 3.60/0.99  inst_num_of_clauses:                    812
% 3.60/0.99  inst_num_in_passive:                    74
% 3.60/0.99  inst_num_in_active:                     454
% 3.60/0.99  inst_num_in_unprocessed:                284
% 3.60/0.99  inst_num_of_loops:                      470
% 3.60/0.99  inst_num_of_learning_restarts:          0
% 3.60/0.99  inst_num_moves_active_passive:          14
% 3.60/0.99  inst_lit_activity:                      0
% 3.60/0.99  inst_lit_activity_moves:                0
% 3.60/0.99  inst_num_tautologies:                   0
% 3.60/0.99  inst_num_prop_implied:                  0
% 3.60/0.99  inst_num_existing_simplified:           0
% 3.60/0.99  inst_num_eq_res_simplified:             0
% 3.60/0.99  inst_num_child_elim:                    0
% 3.60/0.99  inst_num_of_dismatching_blockings:      202
% 3.60/0.99  inst_num_of_non_proper_insts:           759
% 3.60/0.99  inst_num_of_duplicates:                 0
% 3.60/0.99  inst_inst_num_from_inst_to_res:         0
% 3.60/0.99  inst_dismatching_checking_time:         0.
% 3.60/0.99  
% 3.60/0.99  ------ Resolution
% 3.60/0.99  
% 3.60/0.99  res_num_of_clauses:                     0
% 3.60/0.99  res_num_in_passive:                     0
% 3.60/0.99  res_num_in_active:                      0
% 3.60/0.99  res_num_of_loops:                       180
% 3.60/0.99  res_forward_subset_subsumed:            82
% 3.60/0.99  res_backward_subset_subsumed:           0
% 3.60/0.99  res_forward_subsumed:                   0
% 3.60/0.99  res_backward_subsumed:                  0
% 3.60/0.99  res_forward_subsumption_resolution:     2
% 3.60/0.99  res_backward_subsumption_resolution:    0
% 3.60/0.99  res_clause_to_clause_subsumption:       278
% 3.60/0.99  res_orphan_elimination:                 0
% 3.60/0.99  res_tautology_del:                      24
% 3.60/0.99  res_num_eq_res_simplified:              1
% 3.60/0.99  res_num_sel_changes:                    0
% 3.60/0.99  res_moves_from_active_to_pass:          0
% 3.60/0.99  
% 3.60/0.99  ------ Superposition
% 3.60/0.99  
% 3.60/0.99  sup_time_total:                         0.
% 3.60/0.99  sup_time_generating:                    0.
% 3.60/0.99  sup_time_sim_full:                      0.
% 3.60/0.99  sup_time_sim_immed:                     0.
% 3.60/0.99  
% 3.60/0.99  sup_num_of_clauses:                     146
% 3.60/0.99  sup_num_in_active:                      77
% 3.60/0.99  sup_num_in_passive:                     69
% 3.60/0.99  sup_num_of_loops:                       92
% 3.60/0.99  sup_fw_superposition:                   71
% 3.60/0.99  sup_bw_superposition:                   68
% 3.60/0.99  sup_immediate_simplified:               48
% 3.60/0.99  sup_given_eliminated:                   0
% 3.60/0.99  comparisons_done:                       0
% 3.60/0.99  comparisons_avoided:                    0
% 3.60/0.99  
% 3.60/0.99  ------ Simplifications
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  sim_fw_subset_subsumed:                 7
% 3.60/0.99  sim_bw_subset_subsumed:                 6
% 3.60/0.99  sim_fw_subsumed:                        6
% 3.60/0.99  sim_bw_subsumed:                        1
% 3.60/0.99  sim_fw_subsumption_res:                 0
% 3.60/0.99  sim_bw_subsumption_res:                 0
% 3.60/0.99  sim_tautology_del:                      0
% 3.60/0.99  sim_eq_tautology_del:                   8
% 3.60/0.99  sim_eq_res_simp:                        2
% 3.60/0.99  sim_fw_demodulated:                     7
% 3.60/0.99  sim_bw_demodulated:                     11
% 3.60/0.99  sim_light_normalised:                   29
% 3.60/0.99  sim_joinable_taut:                      0
% 3.60/0.99  sim_joinable_simp:                      0
% 3.60/0.99  sim_ac_normalised:                      0
% 3.60/0.99  sim_smt_subsumption:                    0
% 3.60/0.99  
%------------------------------------------------------------------------------

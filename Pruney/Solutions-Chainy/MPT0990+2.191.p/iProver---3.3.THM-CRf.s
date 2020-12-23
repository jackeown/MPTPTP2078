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
% DateTime   : Thu Dec  3 12:03:37 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  182 (2090 expanded)
%              Number of clauses        :  110 ( 567 expanded)
%              Number of leaves         :   20 ( 563 expanded)
%              Depth                    :   23
%              Number of atoms          :  732 (18712 expanded)
%              Number of equality atoms :  370 (6830 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f41,f40])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f33])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1115,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_371,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_14])).

cnf(c_1091,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1200,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1787,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1091,c_34,c_32,c_31,c_29,c_371,c_1200])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1104,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4811,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1104])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4818,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4811,c_35,c_36,c_37])).

cnf(c_4819,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4818])).

cnf(c_4822,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_4819])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_621,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_652,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_622,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1198,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1199,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_4908,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4822,c_38,c_39,c_40,c_25,c_652,c_1199])).

cnf(c_4912,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1115,c_4908])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_375,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_376,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_376])).

cnf(c_1090,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_1637,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1090])).

cnf(c_1794,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1637,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1100,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2581,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1100])).

cnf(c_3211,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2581,c_38,c_39,c_40,c_25,c_652,c_1199])).

cnf(c_4915,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_4912,c_3211])).

cnf(c_1095,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1098,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1106,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3871,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1106])).

cnf(c_4190,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3871,c_38])).

cnf(c_4191,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4190])).

cnf(c_4199,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_4191])).

cnf(c_4200,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4199,c_1787])).

cnf(c_4388,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4200,c_35])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1111,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4390,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4388,c_1111])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1110,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1989,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1095,c_1110])).

cnf(c_1990,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1989,c_28])).

cnf(c_1988,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1098,c_1110])).

cnf(c_1991,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1988,c_1794])).

cnf(c_4391,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4390,c_1990,c_1991])).

cnf(c_4392,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4391])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1116,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2285,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1117])).

cnf(c_2391,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_2285])).

cnf(c_2286,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_1117])).

cnf(c_2394,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_2286])).

cnf(c_1096,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1112,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2494,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1112])).

cnf(c_2562,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2494,c_2391])).

cnf(c_2563,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2562])).

cnf(c_4917,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4912,c_2563])).

cnf(c_4919,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_4915,c_4917])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4920,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_4919,c_3])).

cnf(c_5463,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4392,c_35,c_38,c_2391,c_2394,c_4912,c_4920])).

cnf(c_6374,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_4915,c_4915,c_5463])).

cnf(c_6386,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6374,c_1111])).

cnf(c_2580,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1100])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1161,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1291,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_1515,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_2649,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_34,c_33,c_32,c_28,c_26,c_24,c_1515])).

cnf(c_1093,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2495,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1112])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2567,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2495,c_42,c_2394])).

cnf(c_2651,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2649,c_2567])).

cnf(c_2652,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_2651,c_3])).

cnf(c_6387,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6386,c_1990,c_1991,c_2652])).

cnf(c_6388,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6387])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6388,c_2394,c_2391,c_23,c_42,c_38,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.43/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.43/1.00  
% 3.43/1.00  ------  iProver source info
% 3.43/1.00  
% 3.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.43/1.00  git: non_committed_changes: false
% 3.43/1.00  git: last_make_outside_of_git: false
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    ""
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         true
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     num_symb
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       true
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     true
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.43/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_input_bw                          []
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  ------ Parsing...
% 3.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.43/1.00  ------ Proving...
% 3.43/1.00  ------ Problem Properties 
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  clauses                                 34
% 3.43/1.00  conjectures                             11
% 3.43/1.00  EPR                                     7
% 3.43/1.00  Horn                                    30
% 3.43/1.00  unary                                   17
% 3.43/1.00  binary                                  2
% 3.43/1.00  lits                                    123
% 3.43/1.00  lits eq                                 30
% 3.43/1.00  fd_pure                                 0
% 3.43/1.00  fd_pseudo                               0
% 3.43/1.00  fd_cond                                 4
% 3.43/1.00  fd_pseudo_cond                          1
% 3.43/1.00  AC symbols                              0
% 3.43/1.00  
% 3.43/1.00  ------ Schedule dynamic 5 is on 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  Current options:
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    ""
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         true
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     none
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       false
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     true
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.43/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_input_bw                          []
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ Proving...
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS status Theorem for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  fof(f4,axiom,(
% 3.43/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f48,plain,(
% 3.43/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f4])).
% 3.43/1.00  
% 3.43/1.00  fof(f12,axiom,(
% 3.43/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f59,plain,(
% 3.43/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f12])).
% 3.43/1.00  
% 3.43/1.00  fof(f81,plain,(
% 3.43/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.43/1.00    inference(definition_unfolding,[],[f48,f59])).
% 3.43/1.00  
% 3.43/1.00  fof(f8,axiom,(
% 3.43/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f25,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.43/1.00    inference(ennf_transformation,[],[f8])).
% 3.43/1.00  
% 3.43/1.00  fof(f26,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.00    inference(flattening,[],[f25])).
% 3.43/1.00  
% 3.43/1.00  fof(f39,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.00    inference(nnf_transformation,[],[f26])).
% 3.43/1.00  
% 3.43/1.00  fof(f53,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f39])).
% 3.43/1.00  
% 3.43/1.00  fof(f16,conjecture,(
% 3.43/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f17,negated_conjecture,(
% 3.43/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.43/1.00    inference(negated_conjecture,[],[f16])).
% 3.43/1.00  
% 3.43/1.00  fof(f37,plain,(
% 3.43/1.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.43/1.00    inference(ennf_transformation,[],[f17])).
% 3.43/1.00  
% 3.43/1.00  fof(f38,plain,(
% 3.43/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.43/1.00    inference(flattening,[],[f37])).
% 3.43/1.00  
% 3.43/1.00  fof(f41,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f40,plain,(
% 3.43/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f42,plain,(
% 3.43/1.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f41,f40])).
% 3.43/1.00  
% 3.43/1.00  fof(f74,plain,(
% 3.43/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f10,axiom,(
% 3.43/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f18,plain,(
% 3.43/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.43/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.43/1.00  
% 3.43/1.00  fof(f57,plain,(
% 3.43/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f18])).
% 3.43/1.00  
% 3.43/1.00  fof(f67,plain,(
% 3.43/1.00    v1_funct_1(sK2)),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f69,plain,(
% 3.43/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f70,plain,(
% 3.43/1.00    v1_funct_1(sK3)),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f72,plain,(
% 3.43/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f9,axiom,(
% 3.43/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f27,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.43/1.00    inference(ennf_transformation,[],[f9])).
% 3.43/1.00  
% 3.43/1.00  fof(f28,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.43/1.00    inference(flattening,[],[f27])).
% 3.43/1.00  
% 3.43/1.00  fof(f56,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f28])).
% 3.43/1.00  
% 3.43/1.00  fof(f73,plain,(
% 3.43/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f14,axiom,(
% 3.43/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f33,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.43/1.00    inference(ennf_transformation,[],[f14])).
% 3.43/1.00  
% 3.43/1.00  fof(f34,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.43/1.00    inference(flattening,[],[f33])).
% 3.43/1.00  
% 3.43/1.00  fof(f63,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f34])).
% 3.43/1.00  
% 3.43/1.00  fof(f68,plain,(
% 3.43/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f71,plain,(
% 3.43/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f76,plain,(
% 3.43/1.00    k1_xboole_0 != sK0),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f13,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f31,plain,(
% 3.43/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.43/1.00    inference(ennf_transformation,[],[f13])).
% 3.43/1.00  
% 3.43/1.00  fof(f32,plain,(
% 3.43/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.43/1.00    inference(flattening,[],[f31])).
% 3.43/1.00  
% 3.43/1.00  fof(f60,plain,(
% 3.43/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f32])).
% 3.43/1.00  
% 3.43/1.00  fof(f15,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f35,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.43/1.00    inference(ennf_transformation,[],[f15])).
% 3.43/1.00  
% 3.43/1.00  fof(f36,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.43/1.00    inference(flattening,[],[f35])).
% 3.43/1.00  
% 3.43/1.00  fof(f65,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f36])).
% 3.43/1.00  
% 3.43/1.00  fof(f11,axiom,(
% 3.43/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f29,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.43/1.00    inference(ennf_transformation,[],[f11])).
% 3.43/1.00  
% 3.43/1.00  fof(f30,plain,(
% 3.43/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.43/1.00    inference(flattening,[],[f29])).
% 3.43/1.00  
% 3.43/1.00  fof(f58,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f30])).
% 3.43/1.00  
% 3.43/1.00  fof(f6,axiom,(
% 3.43/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f22,plain,(
% 3.43/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.43/1.00    inference(ennf_transformation,[],[f6])).
% 3.43/1.00  
% 3.43/1.00  fof(f23,plain,(
% 3.43/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.43/1.00    inference(flattening,[],[f22])).
% 3.43/1.00  
% 3.43/1.00  fof(f51,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f23])).
% 3.43/1.00  
% 3.43/1.00  fof(f83,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f51,f59])).
% 3.43/1.00  
% 3.43/1.00  fof(f7,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f24,plain,(
% 3.43/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.43/1.00    inference(ennf_transformation,[],[f7])).
% 3.43/1.00  
% 3.43/1.00  fof(f52,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f24])).
% 3.43/1.00  
% 3.43/1.00  fof(f2,axiom,(
% 3.43/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f44,plain,(
% 3.43/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.43/1.00    inference(cnf_transformation,[],[f2])).
% 3.43/1.00  
% 3.43/1.00  fof(f1,axiom,(
% 3.43/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f19,plain,(
% 3.43/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.43/1.00    inference(ennf_transformation,[],[f1])).
% 3.43/1.00  
% 3.43/1.00  fof(f43,plain,(
% 3.43/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f19])).
% 3.43/1.00  
% 3.43/1.00  fof(f5,axiom,(
% 3.43/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f20,plain,(
% 3.43/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.43/1.00    inference(ennf_transformation,[],[f5])).
% 3.43/1.00  
% 3.43/1.00  fof(f21,plain,(
% 3.43/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.43/1.00    inference(flattening,[],[f20])).
% 3.43/1.00  
% 3.43/1.00  fof(f49,plain,(
% 3.43/1.00    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f21])).
% 3.43/1.00  
% 3.43/1.00  fof(f3,axiom,(
% 3.43/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f45,plain,(
% 3.43/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f3])).
% 3.43/1.00  
% 3.43/1.00  fof(f80,plain,(
% 3.43/1.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.43/1.00    inference(definition_unfolding,[],[f45,f59])).
% 3.43/1.00  
% 3.43/1.00  fof(f75,plain,(
% 3.43/1.00    v2_funct_1(sK2)),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f77,plain,(
% 3.43/1.00    k1_xboole_0 != sK1),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f78,plain,(
% 3.43/1.00    k2_funct_1(sK2) != sK3),
% 3.43/1.00    inference(cnf_transformation,[],[f42])).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4,plain,
% 3.43/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1115,plain,
% 3.43/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_11,plain,
% 3.43/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.43/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.43/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.43/1.00      | X3 = X2 ),
% 3.43/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_27,negated_conjecture,
% 3.43/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_362,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | X3 = X0
% 3.43/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.43/1.00      | k6_partfun1(sK0) != X3
% 3.43/1.00      | sK0 != X2
% 3.43/1.00      | sK0 != X1 ),
% 3.43/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_363,plain,
% 3.43/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.43/1.00      inference(unflattening,[status(thm)],[c_362]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_14,plain,
% 3.43/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.43/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_371,plain,
% 3.43/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.43/1.00      inference(forward_subsumption_resolution,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_363,c_14]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1091,plain,
% 3.43/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.43/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_34,negated_conjecture,
% 3.43/1.00      ( v1_funct_1(sK2) ),
% 3.43/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_32,negated_conjecture,
% 3.43/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.43/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_31,negated_conjecture,
% 3.43/1.00      ( v1_funct_1(sK3) ),
% 3.43/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_29,negated_conjecture,
% 3.43/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.43/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_12,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.43/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | ~ v1_funct_1(X3) ),
% 3.43/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1200,plain,
% 3.43/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.43/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.43/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.43/1.00      | ~ v1_funct_1(sK3)
% 3.43/1.00      | ~ v1_funct_1(sK2) ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1787,plain,
% 3.43/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_1091,c_34,c_32,c_31,c_29,c_371,c_1200]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_28,negated_conjecture,
% 3.43/1.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.43/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_18,plain,
% 3.43/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.43/1.00      | ~ v1_funct_2(X3,X2,X4)
% 3.43/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.43/1.00      | ~ v1_funct_1(X3)
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | v2_funct_1(X3)
% 3.43/1.00      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 3.43/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.43/1.00      | k1_xboole_0 = X4 ),
% 3.43/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1104,plain,
% 3.43/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.43/1.00      | k1_xboole_0 = X3
% 3.43/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.43/1.00      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.43/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.43/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.43/1.00      | v1_funct_1(X2) != iProver_top
% 3.43/1.00      | v1_funct_1(X4) != iProver_top
% 3.43/1.00      | v2_funct_1(X4) = iProver_top
% 3.43/1.00      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4811,plain,
% 3.43/1.00      ( k1_xboole_0 = X0
% 3.43/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.43/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.43/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.43/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.43/1.00      | v1_funct_1(X1) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(X1) = iProver_top
% 3.43/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_28,c_1104]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_35,plain,
% 3.43/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_33,negated_conjecture,
% 3.43/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_36,plain,
% 3.43/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_37,plain,
% 3.43/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4818,plain,
% 3.43/1.00      ( v1_funct_1(X1) != iProver_top
% 3.43/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.43/1.00      | k1_xboole_0 = X0
% 3.43/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.43/1.00      | v2_funct_1(X1) = iProver_top
% 3.43/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_4811,c_35,c_36,c_37]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4819,plain,
% 3.43/1.00      ( k1_xboole_0 = X0
% 3.43/1.00      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.43/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.43/1.00      | v1_funct_1(X1) != iProver_top
% 3.43/1.00      | v2_funct_1(X1) = iProver_top
% 3.43/1.00      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 3.43/1.00      inference(renaming,[status(thm)],[c_4818]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4822,plain,
% 3.43/1.00      ( sK0 = k1_xboole_0
% 3.43/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.43/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.43/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1787,c_4819]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_38,plain,
% 3.43/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_30,negated_conjecture,
% 3.43/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_39,plain,
% 3.43/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_40,plain,
% 3.43/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_25,negated_conjecture,
% 3.43/1.00      ( k1_xboole_0 != sK0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_621,plain,( X0 = X0 ),theory(equality) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_652,plain,
% 3.43/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_621]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_622,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1198,plain,
% 3.43/1.00      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_622]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1199,plain,
% 3.43/1.00      ( sK0 != k1_xboole_0
% 3.43/1.00      | k1_xboole_0 = sK0
% 3.43/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_1198]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4908,plain,
% 3.43/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.43/1.00      | v2_funct_1(sK3) = iProver_top ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_4822,c_38,c_39,c_40,c_25,c_652,c_1199]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4912,plain,
% 3.43/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1115,c_4908]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_16,plain,
% 3.43/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.43/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.43/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.43/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.43/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.43/1.00      | ~ v1_funct_1(X2)
% 3.43/1.00      | ~ v1_funct_1(X3)
% 3.43/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_375,plain,
% 3.43/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.43/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.43/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.43/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | ~ v1_funct_1(X3)
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.43/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.43/1.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.43/1.00      | sK0 != X1 ),
% 3.43/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_376,plain,
% 3.43/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.43/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.43/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.43/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.43/1.00      | ~ v1_funct_1(X2)
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.43/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 3.43/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.43/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_458,plain,
% 3.43/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.43/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.43/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.43/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | ~ v1_funct_1(X2)
% 3.43/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.43/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.43/1.00      inference(equality_resolution_simp,[status(thm)],[c_376]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1090,plain,
% 3.43/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.43/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 3.43/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.43/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.43/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.43/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.43/1.00      | v1_funct_1(X2) != iProver_top
% 3.43/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1637,plain,
% 3.43/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.43/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.43/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.43/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.43/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.43/1.00      inference(equality_resolution,[status(thm)],[c_1090]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1794,plain,
% 3.43/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_1637,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_22,plain,
% 3.43/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.43/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | ~ v2_funct_1(X0)
% 3.43/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.43/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.43/1.00      | k1_xboole_0 = X2 ),
% 3.43/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1100,plain,
% 3.43/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.43/1.00      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.43/1.00      | k1_xboole_0 = X1
% 3.43/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.43/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.43/1.00      | v1_funct_1(X2) != iProver_top
% 3.43/1.00      | v2_funct_1(X2) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2581,plain,
% 3.43/1.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.43/1.00      | sK0 = k1_xboole_0
% 3.43/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.43/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1794,c_1100]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3211,plain,
% 3.43/1.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.43/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_2581,c_38,c_39,c_40,c_25,c_652,c_1199]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4915,plain,
% 3.43/1.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_4912,c_3211]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1095,plain,
% 3.43/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1098,plain,
% 3.43/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_15,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | ~ v1_funct_1(X3)
% 3.43/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1106,plain,
% 3.43/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.43/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.43/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.43/1.00      | v1_funct_1(X5) != iProver_top
% 3.43/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3871,plain,
% 3.43/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.43/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.43/1.00      | v1_funct_1(X2) != iProver_top
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1098,c_1106]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4190,plain,
% 3.43/1.00      ( v1_funct_1(X2) != iProver_top
% 3.43/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.43/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_3871,c_38]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4191,plain,
% 3.43/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.43/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.43/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.43/1.00      inference(renaming,[status(thm)],[c_4190]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4199,plain,
% 3.43/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1095,c_4191]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4200,plain,
% 3.43/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_4199,c_1787]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4388,plain,
% 3.43/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_4200,c_35]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8,plain,
% 3.43/1.00      ( ~ v1_funct_1(X0)
% 3.43/1.00      | ~ v1_funct_1(X1)
% 3.43/1.00      | ~ v2_funct_1(X0)
% 3.43/1.00      | ~ v1_relat_1(X0)
% 3.43/1.00      | ~ v1_relat_1(X1)
% 3.43/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 3.43/1.00      | k2_funct_1(X0) = X1
% 3.43/1.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.43/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1111,plain,
% 3.43/1.00      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.43/1.00      | k2_funct_1(X1) = X0
% 3.43/1.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.43/1.00      | v1_funct_1(X1) != iProver_top
% 3.43/1.00      | v1_funct_1(X0) != iProver_top
% 3.43/1.00      | v2_funct_1(X1) != iProver_top
% 3.43/1.00      | v1_relat_1(X1) != iProver_top
% 3.43/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4390,plain,
% 3.43/1.00      ( k2_funct_1(sK3) = sK2
% 3.43/1.00      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.43/1.00      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_4388,c_1111]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_9,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.43/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1110,plain,
% 3.43/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.43/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1989,plain,
% 3.43/1.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1095,c_1110]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1990,plain,
% 3.43/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_1989,c_28]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1988,plain,
% 3.43/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1098,c_1110]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1991,plain,
% 3.43/1.00      ( k2_relat_1(sK3) = sK0 ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_1988,c_1794]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4391,plain,
% 3.43/1.00      ( k2_funct_1(sK3) = sK2
% 3.43/1.00      | k1_relat_1(sK3) != sK1
% 3.43/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_4390,c_1990,c_1991]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4392,plain,
% 3.43/1.00      ( k2_funct_1(sK3) = sK2
% 3.43/1.00      | k1_relat_1(sK3) != sK1
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.00      inference(equality_resolution_simp,[status(thm)],[c_4391]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1,plain,
% 3.43/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1116,plain,
% 3.43/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_0,plain,
% 3.43/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.43/1.00      | ~ v1_relat_1(X1)
% 3.43/1.00      | v1_relat_1(X0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1117,plain,
% 3.43/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.43/1.00      | v1_relat_1(X1) != iProver_top
% 3.43/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2285,plain,
% 3.43/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1098,c_1117]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2391,plain,
% 3.43/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1116,c_2285]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2286,plain,
% 3.43/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1095,c_1117]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2394,plain,
% 3.43/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1116,c_2286]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1096,plain,
% 3.43/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7,plain,
% 3.43/1.00      ( ~ v1_funct_1(X0)
% 3.43/1.00      | ~ v2_funct_1(X0)
% 3.43/1.00      | ~ v1_relat_1(X0)
% 3.43/1.00      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 3.43/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1112,plain,
% 3.43/1.00      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 3.43/1.00      | v1_funct_1(X0) != iProver_top
% 3.43/1.00      | v2_funct_1(X0) != iProver_top
% 3.43/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2494,plain,
% 3.43/1.00      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 3.43/1.00      | v2_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1096,c_1112]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2562,plain,
% 3.43/1.00      ( v2_funct_1(sK3) != iProver_top
% 3.43/1.00      | k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_2494,c_2391]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2563,plain,
% 3.43/1.00      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 3.43/1.00      | v2_funct_1(sK3) != iProver_top ),
% 3.43/1.00      inference(renaming,[status(thm)],[c_2562]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4917,plain,
% 3.43/1.00      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_4912,c_2563]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4919,plain,
% 3.43/1.00      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_4915,c_4917]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3,plain,
% 3.43/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4920,plain,
% 3.43/1.00      ( k1_relat_1(sK3) = sK1 ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_4919,c_3]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5463,plain,
% 3.43/1.00      ( k2_funct_1(sK3) = sK2 ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_4392,c_35,c_38,c_2391,c_2394,c_4912,c_4920]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6374,plain,
% 3.43/1.00      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 3.43/1.00      inference(light_normalisation,[status(thm)],[c_4915,c_4915,c_5463]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6386,plain,
% 3.43/1.00      ( k2_funct_1(sK2) = sK3
% 3.43/1.00      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 3.43/1.00      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(sK2) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_6374,c_1111]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2580,plain,
% 3.43/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.43/1.00      | sK1 = k1_xboole_0
% 3.43/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.43/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_28,c_1100]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_26,negated_conjecture,
% 3.43/1.00      ( v2_funct_1(sK2) ),
% 3.43/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_24,negated_conjecture,
% 3.43/1.00      ( k1_xboole_0 != sK1 ),
% 3.43/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1161,plain,
% 3.43/1.00      ( ~ v1_funct_2(X0,X1,sK1)
% 3.43/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.43/1.00      | ~ v1_funct_1(X0)
% 3.43/1.00      | ~ v2_funct_1(X0)
% 3.43/1.00      | k2_relset_1(X1,sK1,X0) != sK1
% 3.43/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.43/1.00      | k1_xboole_0 = sK1 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1291,plain,
% 3.43/1.00      ( ~ v1_funct_2(sK2,X0,sK1)
% 3.43/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.43/1.00      | ~ v1_funct_1(sK2)
% 3.43/1.00      | ~ v2_funct_1(sK2)
% 3.43/1.00      | k2_relset_1(X0,sK1,sK2) != sK1
% 3.43/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.43/1.00      | k1_xboole_0 = sK1 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_1161]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1515,plain,
% 3.43/1.00      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.43/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.43/1.00      | ~ v1_funct_1(sK2)
% 3.43/1.00      | ~ v2_funct_1(sK2)
% 3.43/1.00      | k2_relset_1(sK0,sK1,sK2) != sK1
% 3.43/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.43/1.00      | k1_xboole_0 = sK1 ),
% 3.43/1.00      inference(instantiation,[status(thm)],[c_1291]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2649,plain,
% 3.43/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_2580,c_34,c_33,c_32,c_28,c_26,c_24,c_1515]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1093,plain,
% 3.43/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2495,plain,
% 3.43/1.00      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 3.43/1.00      | v2_funct_1(sK2) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1093,c_1112]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_42,plain,
% 3.43/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2567,plain,
% 3.43/1.00      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 3.43/1.00      inference(global_propositional_subsumption,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_2495,c_42,c_2394]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2651,plain,
% 3.43/1.00      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_2649,c_2567]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2652,plain,
% 3.43/1.00      ( k1_relat_1(sK2) = sK0 ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_2651,c_3]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6387,plain,
% 3.43/1.00      ( k2_funct_1(sK2) = sK3
% 3.43/1.00      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 3.43/1.00      | sK0 != sK0
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(sK2) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.00      inference(light_normalisation,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_6386,c_1990,c_1991,c_2652]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6388,plain,
% 3.43/1.00      ( k2_funct_1(sK2) = sK3
% 3.43/1.00      | v1_funct_1(sK3) != iProver_top
% 3.43/1.00      | v1_funct_1(sK2) != iProver_top
% 3.43/1.00      | v2_funct_1(sK2) != iProver_top
% 3.43/1.00      | v1_relat_1(sK3) != iProver_top
% 3.43/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.43/1.00      inference(equality_resolution_simp,[status(thm)],[c_6387]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_23,negated_conjecture,
% 3.43/1.00      ( k2_funct_1(sK2) != sK3 ),
% 3.43/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(contradiction,plain,
% 3.43/1.00      ( $false ),
% 3.43/1.00      inference(minisat,
% 3.43/1.00                [status(thm)],
% 3.43/1.00                [c_6388,c_2394,c_2391,c_23,c_42,c_38,c_35]) ).
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  ------                               Statistics
% 3.43/1.00  
% 3.43/1.00  ------ General
% 3.43/1.00  
% 3.43/1.00  abstr_ref_over_cycles:                  0
% 3.43/1.00  abstr_ref_under_cycles:                 0
% 3.43/1.00  gc_basic_clause_elim:                   0
% 3.43/1.00  forced_gc_time:                         0
% 3.43/1.00  parsing_time:                           0.008
% 3.43/1.00  unif_index_cands_time:                  0.
% 3.43/1.00  unif_index_add_time:                    0.
% 3.43/1.00  orderings_time:                         0.
% 3.43/1.00  out_proof_time:                         0.012
% 3.43/1.00  total_time:                             0.292
% 3.43/1.00  num_of_symbols:                         51
% 3.43/1.00  num_of_terms:                           11004
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing
% 3.43/1.00  
% 3.43/1.00  num_of_splits:                          0
% 3.43/1.00  num_of_split_atoms:                     0
% 3.43/1.00  num_of_reused_defs:                     0
% 3.43/1.00  num_eq_ax_congr_red:                    0
% 3.43/1.00  num_of_sem_filtered_clauses:            1
% 3.43/1.00  num_of_subtypes:                        0
% 3.43/1.00  monotx_restored_types:                  0
% 3.43/1.00  sat_num_of_epr_types:                   0
% 3.43/1.00  sat_num_of_non_cyclic_types:            0
% 3.43/1.00  sat_guarded_non_collapsed_types:        0
% 3.43/1.00  num_pure_diseq_elim:                    0
% 3.43/1.00  simp_replaced_by:                       0
% 3.43/1.00  res_preprocessed:                       170
% 3.43/1.00  prep_upred:                             0
% 3.43/1.00  prep_unflattend:                        12
% 3.43/1.00  smt_new_axioms:                         0
% 3.43/1.00  pred_elim_cands:                        5
% 3.43/1.00  pred_elim:                              1
% 3.43/1.00  pred_elim_cl:                           1
% 3.43/1.00  pred_elim_cycles:                       3
% 3.43/1.00  merged_defs:                            0
% 3.43/1.00  merged_defs_ncl:                        0
% 3.43/1.00  bin_hyper_res:                          0
% 3.43/1.00  prep_cycles:                            4
% 3.43/1.00  pred_elim_time:                         0.003
% 3.43/1.00  splitting_time:                         0.
% 3.43/1.00  sem_filter_time:                        0.
% 3.43/1.00  monotx_time:                            0.
% 3.43/1.00  subtype_inf_time:                       0.
% 3.43/1.00  
% 3.43/1.00  ------ Problem properties
% 3.43/1.00  
% 3.43/1.00  clauses:                                34
% 3.43/1.00  conjectures:                            11
% 3.43/1.00  epr:                                    7
% 3.43/1.00  horn:                                   30
% 3.43/1.00  ground:                                 12
% 3.43/1.00  unary:                                  17
% 3.43/1.00  binary:                                 2
% 3.43/1.00  lits:                                   123
% 3.43/1.00  lits_eq:                                30
% 3.43/1.00  fd_pure:                                0
% 3.43/1.00  fd_pseudo:                              0
% 3.43/1.00  fd_cond:                                4
% 3.43/1.00  fd_pseudo_cond:                         1
% 3.43/1.00  ac_symbols:                             0
% 3.43/1.00  
% 3.43/1.00  ------ Propositional Solver
% 3.43/1.00  
% 3.43/1.00  prop_solver_calls:                      29
% 3.43/1.00  prop_fast_solver_calls:                 1593
% 3.43/1.00  smt_solver_calls:                       0
% 3.43/1.00  smt_fast_solver_calls:                  0
% 3.43/1.00  prop_num_of_clauses:                    3554
% 3.43/1.00  prop_preprocess_simplified:             8443
% 3.43/1.00  prop_fo_subsumed:                       91
% 3.43/1.00  prop_solver_time:                       0.
% 3.43/1.00  smt_solver_time:                        0.
% 3.43/1.00  smt_fast_solver_time:                   0.
% 3.43/1.00  prop_fast_solver_time:                  0.
% 3.43/1.00  prop_unsat_core_time:                   0.
% 3.43/1.00  
% 3.43/1.00  ------ QBF
% 3.43/1.00  
% 3.43/1.00  qbf_q_res:                              0
% 3.43/1.00  qbf_num_tautologies:                    0
% 3.43/1.00  qbf_prep_cycles:                        0
% 3.43/1.00  
% 3.43/1.00  ------ BMC1
% 3.43/1.00  
% 3.43/1.00  bmc1_current_bound:                     -1
% 3.43/1.00  bmc1_last_solved_bound:                 -1
% 3.43/1.00  bmc1_unsat_core_size:                   -1
% 3.43/1.00  bmc1_unsat_core_parents_size:           -1
% 3.43/1.00  bmc1_merge_next_fun:                    0
% 3.43/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation
% 3.43/1.00  
% 3.43/1.00  inst_num_of_clauses:                    876
% 3.43/1.00  inst_num_in_passive:                    68
% 3.43/1.00  inst_num_in_active:                     467
% 3.43/1.00  inst_num_in_unprocessed:                341
% 3.43/1.00  inst_num_of_loops:                      480
% 3.43/1.00  inst_num_of_learning_restarts:          0
% 3.43/1.00  inst_num_moves_active_passive:          11
% 3.43/1.00  inst_lit_activity:                      0
% 3.43/1.00  inst_lit_activity_moves:                0
% 3.43/1.00  inst_num_tautologies:                   0
% 3.43/1.00  inst_num_prop_implied:                  0
% 3.43/1.00  inst_num_existing_simplified:           0
% 3.43/1.00  inst_num_eq_res_simplified:             0
% 3.43/1.00  inst_num_child_elim:                    0
% 3.43/1.00  inst_num_of_dismatching_blockings:      74
% 3.43/1.00  inst_num_of_non_proper_insts:           838
% 3.43/1.00  inst_num_of_duplicates:                 0
% 3.43/1.00  inst_inst_num_from_inst_to_res:         0
% 3.43/1.00  inst_dismatching_checking_time:         0.
% 3.43/1.00  
% 3.43/1.00  ------ Resolution
% 3.43/1.00  
% 3.43/1.00  res_num_of_clauses:                     0
% 3.43/1.00  res_num_in_passive:                     0
% 3.43/1.00  res_num_in_active:                      0
% 3.43/1.00  res_num_of_loops:                       174
% 3.43/1.00  res_forward_subset_subsumed:            51
% 3.43/1.00  res_backward_subset_subsumed:           0
% 3.43/1.00  res_forward_subsumed:                   0
% 3.43/1.00  res_backward_subsumed:                  0
% 3.43/1.00  res_forward_subsumption_resolution:     2
% 3.43/1.00  res_backward_subsumption_resolution:    0
% 3.43/1.00  res_clause_to_clause_subsumption:       299
% 3.43/1.00  res_orphan_elimination:                 0
% 3.43/1.00  res_tautology_del:                      27
% 3.43/1.00  res_num_eq_res_simplified:              1
% 3.43/1.00  res_num_sel_changes:                    0
% 3.43/1.00  res_moves_from_active_to_pass:          0
% 3.43/1.00  
% 3.43/1.00  ------ Superposition
% 3.43/1.00  
% 3.43/1.00  sup_time_total:                         0.
% 3.43/1.00  sup_time_generating:                    0.
% 3.43/1.00  sup_time_sim_full:                      0.
% 3.43/1.00  sup_time_sim_immed:                     0.
% 3.43/1.00  
% 3.43/1.00  sup_num_of_clauses:                     145
% 3.43/1.00  sup_num_in_active:                      75
% 3.43/1.00  sup_num_in_passive:                     70
% 3.43/1.00  sup_num_of_loops:                       94
% 3.43/1.00  sup_fw_superposition:                   82
% 3.43/1.00  sup_bw_superposition:                   67
% 3.43/1.00  sup_immediate_simplified:               63
% 3.43/1.00  sup_given_eliminated:                   0
% 3.43/1.00  comparisons_done:                       0
% 3.43/1.00  comparisons_avoided:                    2
% 3.43/1.00  
% 3.43/1.00  ------ Simplifications
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  sim_fw_subset_subsumed:                 5
% 3.43/1.00  sim_bw_subset_subsumed:                 14
% 3.43/1.00  sim_fw_subsumed:                        6
% 3.43/1.00  sim_bw_subsumed:                        3
% 3.43/1.00  sim_fw_subsumption_res:                 0
% 3.43/1.00  sim_bw_subsumption_res:                 0
% 3.43/1.00  sim_tautology_del:                      0
% 3.43/1.00  sim_eq_tautology_del:                   13
% 3.43/1.00  sim_eq_res_simp:                        2
% 3.43/1.00  sim_fw_demodulated:                     10
% 3.43/1.00  sim_bw_demodulated:                     13
% 3.43/1.00  sim_light_normalised:                   41
% 3.43/1.00  sim_joinable_taut:                      0
% 3.43/1.00  sim_joinable_simp:                      0
% 3.43/1.00  sim_ac_normalised:                      0
% 3.43/1.00  sim_smt_subsumption:                    0
% 3.43/1.00  
%------------------------------------------------------------------------------

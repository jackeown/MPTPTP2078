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
% DateTime   : Thu Dec  3 12:01:50 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 770 expanded)
%              Number of clauses        :   92 ( 236 expanded)
%              Number of leaves         :   21 ( 189 expanded)
%              Depth                    :   21
%              Number of atoms          :  566 (4883 expanded)
%              Number of equality atoms :  211 ( 410 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f46,f45])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f69])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_444,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_452,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_444,c_20])).

cnf(c_1143,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_4289,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_1143])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4881,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4289,c_32,c_34,c_35,c_37])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1153,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4907,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4881,c_1153])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1152,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1158,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3208,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1152,c_1158])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_456,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_534,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_457])).

cnf(c_1142,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2128,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1142])).

cnf(c_2207,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2128,c_32,c_33,c_34,c_35,c_36,c_37])).

cnf(c_3223,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3208,c_2207])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_327,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_328,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_338,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_328,c_11])).

cnf(c_24,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_24])).

cnf(c_354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_701,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_354])).

cnf(c_1145,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_3302,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3223,c_1145])).

cnf(c_3303,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3302])).

cnf(c_700,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_354])).

cnf(c_1146,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_3301,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3223,c_1146])).

cnf(c_3471,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_3301])).

cnf(c_6060,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4907,c_32,c_33,c_34,c_35,c_36,c_37,c_3303,c_3471])).

cnf(c_6061,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6060])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1160,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6066,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6061,c_1160])).

cnf(c_1149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6077,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6066,c_1149])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6085,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6077,c_3])).

cnf(c_712,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2835,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_2836,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2835])).

cnf(c_2838,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2836])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2700,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2701,plain,
    ( sK2 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2700])).

cnf(c_2703,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2701])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2466,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2467,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2466])).

cnf(c_2469,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1672,plain,
    ( ~ v1_relat_1(k6_partfun1(X0))
    | k2_relat_1(k6_partfun1(X0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1676,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
    | k2_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_1415,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_1416,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1415])).

cnf(c_1418,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_1400,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1402,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_96,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_83,plain,
    ( k2_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_81,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_50,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6085,c_3471,c_3303,c_2838,c_2703,c_2469,c_1676,c_1418,c_1402,c_96,c_83,c_81,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.23/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.99  
% 3.23/0.99  ------  iProver source info
% 3.23/0.99  
% 3.23/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.99  git: non_committed_changes: false
% 3.23/0.99  git: last_make_outside_of_git: false
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options
% 3.23/0.99  
% 3.23/0.99  --out_options                           all
% 3.23/0.99  --tptp_safe_out                         true
% 3.23/0.99  --problem_path                          ""
% 3.23/0.99  --include_path                          ""
% 3.23/0.99  --clausifier                            res/vclausify_rel
% 3.23/0.99  --clausifier_options                    --mode clausify
% 3.23/0.99  --stdin                                 false
% 3.23/0.99  --stats_out                             all
% 3.23/0.99  
% 3.23/0.99  ------ General Options
% 3.23/0.99  
% 3.23/0.99  --fof                                   false
% 3.23/0.99  --time_out_real                         305.
% 3.23/0.99  --time_out_virtual                      -1.
% 3.23/0.99  --symbol_type_check                     false
% 3.23/0.99  --clausify_out                          false
% 3.23/0.99  --sig_cnt_out                           false
% 3.23/0.99  --trig_cnt_out                          false
% 3.23/0.99  --trig_cnt_out_tolerance                1.
% 3.23/0.99  --trig_cnt_out_sk_spl                   false
% 3.23/0.99  --abstr_cl_out                          false
% 3.23/0.99  
% 3.23/0.99  ------ Global Options
% 3.23/0.99  
% 3.23/0.99  --schedule                              default
% 3.23/0.99  --add_important_lit                     false
% 3.23/0.99  --prop_solver_per_cl                    1000
% 3.23/0.99  --min_unsat_core                        false
% 3.23/0.99  --soft_assumptions                      false
% 3.23/0.99  --soft_lemma_size                       3
% 3.23/0.99  --prop_impl_unit_size                   0
% 3.23/0.99  --prop_impl_unit                        []
% 3.23/0.99  --share_sel_clauses                     true
% 3.23/0.99  --reset_solvers                         false
% 3.23/0.99  --bc_imp_inh                            [conj_cone]
% 3.23/0.99  --conj_cone_tolerance                   3.
% 3.23/0.99  --extra_neg_conj                        none
% 3.23/0.99  --large_theory_mode                     true
% 3.23/0.99  --prolific_symb_bound                   200
% 3.23/0.99  --lt_threshold                          2000
% 3.23/0.99  --clause_weak_htbl                      true
% 3.23/0.99  --gc_record_bc_elim                     false
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing Options
% 3.23/0.99  
% 3.23/0.99  --preprocessing_flag                    true
% 3.23/0.99  --time_out_prep_mult                    0.1
% 3.23/0.99  --splitting_mode                        input
% 3.23/0.99  --splitting_grd                         true
% 3.23/0.99  --splitting_cvd                         false
% 3.23/0.99  --splitting_cvd_svl                     false
% 3.23/0.99  --splitting_nvd                         32
% 3.23/0.99  --sub_typing                            true
% 3.23/0.99  --prep_gs_sim                           true
% 3.23/0.99  --prep_unflatten                        true
% 3.23/0.99  --prep_res_sim                          true
% 3.23/0.99  --prep_upred                            true
% 3.23/0.99  --prep_sem_filter                       exhaustive
% 3.23/0.99  --prep_sem_filter_out                   false
% 3.23/0.99  --pred_elim                             true
% 3.23/0.99  --res_sim_input                         true
% 3.23/0.99  --eq_ax_congr_red                       true
% 3.23/0.99  --pure_diseq_elim                       true
% 3.23/0.99  --brand_transform                       false
% 3.23/0.99  --non_eq_to_eq                          false
% 3.23/0.99  --prep_def_merge                        true
% 3.23/0.99  --prep_def_merge_prop_impl              false
% 3.23/0.99  --prep_def_merge_mbd                    true
% 3.23/0.99  --prep_def_merge_tr_red                 false
% 3.23/0.99  --prep_def_merge_tr_cl                  false
% 3.23/0.99  --smt_preprocessing                     true
% 3.23/0.99  --smt_ac_axioms                         fast
% 3.23/0.99  --preprocessed_out                      false
% 3.23/0.99  --preprocessed_stats                    false
% 3.23/0.99  
% 3.23/0.99  ------ Abstraction refinement Options
% 3.23/0.99  
% 3.23/0.99  --abstr_ref                             []
% 3.23/0.99  --abstr_ref_prep                        false
% 3.23/0.99  --abstr_ref_until_sat                   false
% 3.23/0.99  --abstr_ref_sig_restrict                funpre
% 3.23/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.99  --abstr_ref_under                       []
% 3.23/0.99  
% 3.23/0.99  ------ SAT Options
% 3.23/0.99  
% 3.23/0.99  --sat_mode                              false
% 3.23/0.99  --sat_fm_restart_options                ""
% 3.23/0.99  --sat_gr_def                            false
% 3.23/0.99  --sat_epr_types                         true
% 3.23/0.99  --sat_non_cyclic_types                  false
% 3.23/0.99  --sat_finite_models                     false
% 3.23/0.99  --sat_fm_lemmas                         false
% 3.23/0.99  --sat_fm_prep                           false
% 3.23/0.99  --sat_fm_uc_incr                        true
% 3.23/0.99  --sat_out_model                         small
% 3.23/0.99  --sat_out_clauses                       false
% 3.23/0.99  
% 3.23/0.99  ------ QBF Options
% 3.23/0.99  
% 3.23/0.99  --qbf_mode                              false
% 3.23/0.99  --qbf_elim_univ                         false
% 3.23/0.99  --qbf_dom_inst                          none
% 3.23/0.99  --qbf_dom_pre_inst                      false
% 3.23/0.99  --qbf_sk_in                             false
% 3.23/0.99  --qbf_pred_elim                         true
% 3.23/0.99  --qbf_split                             512
% 3.23/0.99  
% 3.23/0.99  ------ BMC1 Options
% 3.23/0.99  
% 3.23/0.99  --bmc1_incremental                      false
% 3.23/0.99  --bmc1_axioms                           reachable_all
% 3.23/0.99  --bmc1_min_bound                        0
% 3.23/0.99  --bmc1_max_bound                        -1
% 3.23/0.99  --bmc1_max_bound_default                -1
% 3.23/0.99  --bmc1_symbol_reachability              true
% 3.23/0.99  --bmc1_property_lemmas                  false
% 3.23/0.99  --bmc1_k_induction                      false
% 3.23/0.99  --bmc1_non_equiv_states                 false
% 3.23/0.99  --bmc1_deadlock                         false
% 3.23/0.99  --bmc1_ucm                              false
% 3.23/0.99  --bmc1_add_unsat_core                   none
% 3.23/0.99  --bmc1_unsat_core_children              false
% 3.23/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.99  --bmc1_out_stat                         full
% 3.23/0.99  --bmc1_ground_init                      false
% 3.23/0.99  --bmc1_pre_inst_next_state              false
% 3.23/0.99  --bmc1_pre_inst_state                   false
% 3.23/0.99  --bmc1_pre_inst_reach_state             false
% 3.23/0.99  --bmc1_out_unsat_core                   false
% 3.23/0.99  --bmc1_aig_witness_out                  false
% 3.23/0.99  --bmc1_verbose                          false
% 3.23/0.99  --bmc1_dump_clauses_tptp                false
% 3.23/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.99  --bmc1_dump_file                        -
% 3.23/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.99  --bmc1_ucm_extend_mode                  1
% 3.23/0.99  --bmc1_ucm_init_mode                    2
% 3.23/0.99  --bmc1_ucm_cone_mode                    none
% 3.23/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.99  --bmc1_ucm_relax_model                  4
% 3.23/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.99  --bmc1_ucm_layered_model                none
% 3.23/0.99  --bmc1_ucm_max_lemma_size               10
% 3.23/0.99  
% 3.23/0.99  ------ AIG Options
% 3.23/0.99  
% 3.23/0.99  --aig_mode                              false
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation Options
% 3.23/0.99  
% 3.23/0.99  --instantiation_flag                    true
% 3.23/0.99  --inst_sos_flag                         false
% 3.23/0.99  --inst_sos_phase                        true
% 3.23/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel_side                     num_symb
% 3.23/0.99  --inst_solver_per_active                1400
% 3.23/0.99  --inst_solver_calls_frac                1.
% 3.23/0.99  --inst_passive_queue_type               priority_queues
% 3.23/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.99  --inst_passive_queues_freq              [25;2]
% 3.23/0.99  --inst_dismatching                      true
% 3.23/0.99  --inst_eager_unprocessed_to_passive     true
% 3.23/0.99  --inst_prop_sim_given                   true
% 3.23/0.99  --inst_prop_sim_new                     false
% 3.23/0.99  --inst_subs_new                         false
% 3.23/0.99  --inst_eq_res_simp                      false
% 3.23/0.99  --inst_subs_given                       false
% 3.23/0.99  --inst_orphan_elimination               true
% 3.23/0.99  --inst_learning_loop_flag               true
% 3.23/0.99  --inst_learning_start                   3000
% 3.23/0.99  --inst_learning_factor                  2
% 3.23/0.99  --inst_start_prop_sim_after_learn       3
% 3.23/0.99  --inst_sel_renew                        solver
% 3.23/0.99  --inst_lit_activity_flag                true
% 3.23/0.99  --inst_restr_to_given                   false
% 3.23/0.99  --inst_activity_threshold               500
% 3.23/0.99  --inst_out_proof                        true
% 3.23/0.99  
% 3.23/0.99  ------ Resolution Options
% 3.23/0.99  
% 3.23/0.99  --resolution_flag                       true
% 3.23/0.99  --res_lit_sel                           adaptive
% 3.23/0.99  --res_lit_sel_side                      none
% 3.23/0.99  --res_ordering                          kbo
% 3.23/0.99  --res_to_prop_solver                    active
% 3.23/0.99  --res_prop_simpl_new                    false
% 3.23/0.99  --res_prop_simpl_given                  true
% 3.23/0.99  --res_passive_queue_type                priority_queues
% 3.23/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.99  --res_passive_queues_freq               [15;5]
% 3.23/0.99  --res_forward_subs                      full
% 3.23/0.99  --res_backward_subs                     full
% 3.23/0.99  --res_forward_subs_resolution           true
% 3.23/0.99  --res_backward_subs_resolution          true
% 3.23/0.99  --res_orphan_elimination                true
% 3.23/0.99  --res_time_limit                        2.
% 3.23/0.99  --res_out_proof                         true
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Options
% 3.23/0.99  
% 3.23/0.99  --superposition_flag                    true
% 3.23/0.99  --sup_passive_queue_type                priority_queues
% 3.23/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.99  --demod_completeness_check              fast
% 3.23/0.99  --demod_use_ground                      true
% 3.23/0.99  --sup_to_prop_solver                    passive
% 3.23/0.99  --sup_prop_simpl_new                    true
% 3.23/0.99  --sup_prop_simpl_given                  true
% 3.23/0.99  --sup_fun_splitting                     false
% 3.23/0.99  --sup_smt_interval                      50000
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Simplification Setup
% 3.23/0.99  
% 3.23/0.99  --sup_indices_passive                   []
% 3.23/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_full_bw                           [BwDemod]
% 3.23/0.99  --sup_immed_triv                        [TrivRules]
% 3.23/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_immed_bw_main                     []
% 3.23/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  
% 3.23/0.99  ------ Combination Options
% 3.23/0.99  
% 3.23/0.99  --comb_res_mult                         3
% 3.23/0.99  --comb_sup_mult                         2
% 3.23/0.99  --comb_inst_mult                        10
% 3.23/0.99  
% 3.23/0.99  ------ Debug Options
% 3.23/0.99  
% 3.23/0.99  --dbg_backtrace                         false
% 3.23/0.99  --dbg_dump_prop_clauses                 false
% 3.23/0.99  --dbg_dump_prop_clauses_file            -
% 3.23/0.99  --dbg_out_stat                          false
% 3.23/0.99  ------ Parsing...
% 3.23/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/0.99  ------ Proving...
% 3.23/0.99  ------ Problem Properties 
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  clauses                                 29
% 3.23/0.99  conjectures                             6
% 3.23/0.99  EPR                                     6
% 3.23/0.99  Horn                                    27
% 3.23/0.99  unary                                   13
% 3.23/0.99  binary                                  4
% 3.23/0.99  lits                                    82
% 3.23/0.99  lits eq                                 20
% 3.23/0.99  fd_pure                                 0
% 3.23/0.99  fd_pseudo                               0
% 3.23/0.99  fd_cond                                 4
% 3.23/0.99  fd_pseudo_cond                          1
% 3.23/0.99  AC symbols                              0
% 3.23/0.99  
% 3.23/0.99  ------ Schedule dynamic 5 is on 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  Current options:
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options
% 3.23/0.99  
% 3.23/0.99  --out_options                           all
% 3.23/0.99  --tptp_safe_out                         true
% 3.23/0.99  --problem_path                          ""
% 3.23/0.99  --include_path                          ""
% 3.23/0.99  --clausifier                            res/vclausify_rel
% 3.23/0.99  --clausifier_options                    --mode clausify
% 3.23/0.99  --stdin                                 false
% 3.23/0.99  --stats_out                             all
% 3.23/0.99  
% 3.23/0.99  ------ General Options
% 3.23/0.99  
% 3.23/0.99  --fof                                   false
% 3.23/0.99  --time_out_real                         305.
% 3.23/0.99  --time_out_virtual                      -1.
% 3.23/0.99  --symbol_type_check                     false
% 3.23/0.99  --clausify_out                          false
% 3.23/0.99  --sig_cnt_out                           false
% 3.23/0.99  --trig_cnt_out                          false
% 3.23/0.99  --trig_cnt_out_tolerance                1.
% 3.23/0.99  --trig_cnt_out_sk_spl                   false
% 3.23/0.99  --abstr_cl_out                          false
% 3.23/0.99  
% 3.23/0.99  ------ Global Options
% 3.23/0.99  
% 3.23/0.99  --schedule                              default
% 3.23/0.99  --add_important_lit                     false
% 3.23/0.99  --prop_solver_per_cl                    1000
% 3.23/0.99  --min_unsat_core                        false
% 3.23/0.99  --soft_assumptions                      false
% 3.23/0.99  --soft_lemma_size                       3
% 3.23/0.99  --prop_impl_unit_size                   0
% 3.23/0.99  --prop_impl_unit                        []
% 3.23/0.99  --share_sel_clauses                     true
% 3.23/0.99  --reset_solvers                         false
% 3.23/0.99  --bc_imp_inh                            [conj_cone]
% 3.23/0.99  --conj_cone_tolerance                   3.
% 3.23/0.99  --extra_neg_conj                        none
% 3.23/0.99  --large_theory_mode                     true
% 3.23/0.99  --prolific_symb_bound                   200
% 3.23/0.99  --lt_threshold                          2000
% 3.23/0.99  --clause_weak_htbl                      true
% 3.23/0.99  --gc_record_bc_elim                     false
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing Options
% 3.23/0.99  
% 3.23/0.99  --preprocessing_flag                    true
% 3.23/0.99  --time_out_prep_mult                    0.1
% 3.23/0.99  --splitting_mode                        input
% 3.23/0.99  --splitting_grd                         true
% 3.23/0.99  --splitting_cvd                         false
% 3.23/0.99  --splitting_cvd_svl                     false
% 3.23/0.99  --splitting_nvd                         32
% 3.23/0.99  --sub_typing                            true
% 3.23/0.99  --prep_gs_sim                           true
% 3.23/0.99  --prep_unflatten                        true
% 3.23/0.99  --prep_res_sim                          true
% 3.23/0.99  --prep_upred                            true
% 3.23/0.99  --prep_sem_filter                       exhaustive
% 3.23/0.99  --prep_sem_filter_out                   false
% 3.23/0.99  --pred_elim                             true
% 3.23/0.99  --res_sim_input                         true
% 3.23/0.99  --eq_ax_congr_red                       true
% 3.23/0.99  --pure_diseq_elim                       true
% 3.23/0.99  --brand_transform                       false
% 3.23/0.99  --non_eq_to_eq                          false
% 3.23/0.99  --prep_def_merge                        true
% 3.23/0.99  --prep_def_merge_prop_impl              false
% 3.23/0.99  --prep_def_merge_mbd                    true
% 3.23/0.99  --prep_def_merge_tr_red                 false
% 3.23/0.99  --prep_def_merge_tr_cl                  false
% 3.23/0.99  --smt_preprocessing                     true
% 3.23/0.99  --smt_ac_axioms                         fast
% 3.23/0.99  --preprocessed_out                      false
% 3.23/0.99  --preprocessed_stats                    false
% 3.23/0.99  
% 3.23/0.99  ------ Abstraction refinement Options
% 3.23/0.99  
% 3.23/0.99  --abstr_ref                             []
% 3.23/0.99  --abstr_ref_prep                        false
% 3.23/0.99  --abstr_ref_until_sat                   false
% 3.23/0.99  --abstr_ref_sig_restrict                funpre
% 3.23/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.99  --abstr_ref_under                       []
% 3.23/0.99  
% 3.23/0.99  ------ SAT Options
% 3.23/0.99  
% 3.23/0.99  --sat_mode                              false
% 3.23/0.99  --sat_fm_restart_options                ""
% 3.23/0.99  --sat_gr_def                            false
% 3.23/0.99  --sat_epr_types                         true
% 3.23/0.99  --sat_non_cyclic_types                  false
% 3.23/0.99  --sat_finite_models                     false
% 3.23/0.99  --sat_fm_lemmas                         false
% 3.23/0.99  --sat_fm_prep                           false
% 3.23/0.99  --sat_fm_uc_incr                        true
% 3.23/0.99  --sat_out_model                         small
% 3.23/0.99  --sat_out_clauses                       false
% 3.23/0.99  
% 3.23/0.99  ------ QBF Options
% 3.23/0.99  
% 3.23/0.99  --qbf_mode                              false
% 3.23/0.99  --qbf_elim_univ                         false
% 3.23/0.99  --qbf_dom_inst                          none
% 3.23/0.99  --qbf_dom_pre_inst                      false
% 3.23/0.99  --qbf_sk_in                             false
% 3.23/0.99  --qbf_pred_elim                         true
% 3.23/0.99  --qbf_split                             512
% 3.23/0.99  
% 3.23/0.99  ------ BMC1 Options
% 3.23/0.99  
% 3.23/0.99  --bmc1_incremental                      false
% 3.23/0.99  --bmc1_axioms                           reachable_all
% 3.23/0.99  --bmc1_min_bound                        0
% 3.23/0.99  --bmc1_max_bound                        -1
% 3.23/0.99  --bmc1_max_bound_default                -1
% 3.23/0.99  --bmc1_symbol_reachability              true
% 3.23/0.99  --bmc1_property_lemmas                  false
% 3.23/0.99  --bmc1_k_induction                      false
% 3.23/0.99  --bmc1_non_equiv_states                 false
% 3.23/0.99  --bmc1_deadlock                         false
% 3.23/0.99  --bmc1_ucm                              false
% 3.23/0.99  --bmc1_add_unsat_core                   none
% 3.23/0.99  --bmc1_unsat_core_children              false
% 3.23/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.99  --bmc1_out_stat                         full
% 3.23/0.99  --bmc1_ground_init                      false
% 3.23/0.99  --bmc1_pre_inst_next_state              false
% 3.23/0.99  --bmc1_pre_inst_state                   false
% 3.23/0.99  --bmc1_pre_inst_reach_state             false
% 3.23/0.99  --bmc1_out_unsat_core                   false
% 3.23/0.99  --bmc1_aig_witness_out                  false
% 3.23/0.99  --bmc1_verbose                          false
% 3.23/0.99  --bmc1_dump_clauses_tptp                false
% 3.23/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.99  --bmc1_dump_file                        -
% 3.23/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.99  --bmc1_ucm_extend_mode                  1
% 3.23/0.99  --bmc1_ucm_init_mode                    2
% 3.23/0.99  --bmc1_ucm_cone_mode                    none
% 3.23/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.99  --bmc1_ucm_relax_model                  4
% 3.23/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.99  --bmc1_ucm_layered_model                none
% 3.23/0.99  --bmc1_ucm_max_lemma_size               10
% 3.23/0.99  
% 3.23/0.99  ------ AIG Options
% 3.23/0.99  
% 3.23/0.99  --aig_mode                              false
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation Options
% 3.23/0.99  
% 3.23/0.99  --instantiation_flag                    true
% 3.23/0.99  --inst_sos_flag                         false
% 3.23/0.99  --inst_sos_phase                        true
% 3.23/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel_side                     none
% 3.23/0.99  --inst_solver_per_active                1400
% 3.23/0.99  --inst_solver_calls_frac                1.
% 3.23/0.99  --inst_passive_queue_type               priority_queues
% 3.23/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.99  --inst_passive_queues_freq              [25;2]
% 3.23/0.99  --inst_dismatching                      true
% 3.23/0.99  --inst_eager_unprocessed_to_passive     true
% 3.23/0.99  --inst_prop_sim_given                   true
% 3.23/0.99  --inst_prop_sim_new                     false
% 3.23/0.99  --inst_subs_new                         false
% 3.23/0.99  --inst_eq_res_simp                      false
% 3.23/0.99  --inst_subs_given                       false
% 3.23/0.99  --inst_orphan_elimination               true
% 3.23/0.99  --inst_learning_loop_flag               true
% 3.23/0.99  --inst_learning_start                   3000
% 3.23/0.99  --inst_learning_factor                  2
% 3.23/0.99  --inst_start_prop_sim_after_learn       3
% 3.23/0.99  --inst_sel_renew                        solver
% 3.23/0.99  --inst_lit_activity_flag                true
% 3.23/0.99  --inst_restr_to_given                   false
% 3.23/0.99  --inst_activity_threshold               500
% 3.23/0.99  --inst_out_proof                        true
% 3.23/0.99  
% 3.23/0.99  ------ Resolution Options
% 3.23/0.99  
% 3.23/0.99  --resolution_flag                       false
% 3.23/0.99  --res_lit_sel                           adaptive
% 3.23/0.99  --res_lit_sel_side                      none
% 3.23/0.99  --res_ordering                          kbo
% 3.23/0.99  --res_to_prop_solver                    active
% 3.23/0.99  --res_prop_simpl_new                    false
% 3.23/0.99  --res_prop_simpl_given                  true
% 3.23/0.99  --res_passive_queue_type                priority_queues
% 3.23/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.99  --res_passive_queues_freq               [15;5]
% 3.23/0.99  --res_forward_subs                      full
% 3.23/0.99  --res_backward_subs                     full
% 3.23/0.99  --res_forward_subs_resolution           true
% 3.23/0.99  --res_backward_subs_resolution          true
% 3.23/0.99  --res_orphan_elimination                true
% 3.23/0.99  --res_time_limit                        2.
% 3.23/0.99  --res_out_proof                         true
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Options
% 3.23/0.99  
% 3.23/0.99  --superposition_flag                    true
% 3.23/0.99  --sup_passive_queue_type                priority_queues
% 3.23/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.99  --demod_completeness_check              fast
% 3.23/0.99  --demod_use_ground                      true
% 3.23/0.99  --sup_to_prop_solver                    passive
% 3.23/0.99  --sup_prop_simpl_new                    true
% 3.23/0.99  --sup_prop_simpl_given                  true
% 3.23/0.99  --sup_fun_splitting                     false
% 3.23/0.99  --sup_smt_interval                      50000
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Simplification Setup
% 3.23/0.99  
% 3.23/0.99  --sup_indices_passive                   []
% 3.23/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_full_bw                           [BwDemod]
% 3.23/0.99  --sup_immed_triv                        [TrivRules]
% 3.23/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_immed_bw_main                     []
% 3.23/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  
% 3.23/0.99  ------ Combination Options
% 3.23/0.99  
% 3.23/0.99  --comb_res_mult                         3
% 3.23/0.99  --comb_sup_mult                         2
% 3.23/0.99  --comb_inst_mult                        10
% 3.23/0.99  
% 3.23/0.99  ------ Debug Options
% 3.23/0.99  
% 3.23/0.99  --dbg_backtrace                         false
% 3.23/0.99  --dbg_dump_prop_clauses                 false
% 3.23/0.99  --dbg_dump_prop_clauses_file            -
% 3.23/0.99  --dbg_out_stat                          false
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ Proving...
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS status Theorem for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  fof(f13,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f33,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.23/0.99    inference(ennf_transformation,[],[f13])).
% 3.23/0.99  
% 3.23/0.99  fof(f34,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.23/0.99    inference(flattening,[],[f33])).
% 3.23/0.99  
% 3.23/0.99  fof(f67,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f34])).
% 3.23/0.99  
% 3.23/0.99  fof(f11,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f29,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.23/0.99    inference(ennf_transformation,[],[f11])).
% 3.23/0.99  
% 3.23/0.99  fof(f30,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(flattening,[],[f29])).
% 3.23/0.99  
% 3.23/0.99  fof(f43,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(nnf_transformation,[],[f30])).
% 3.23/0.99  
% 3.23/0.99  fof(f62,plain,(
% 3.23/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f43])).
% 3.23/0.99  
% 3.23/0.99  fof(f18,conjecture,(
% 3.23/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f19,negated_conjecture,(
% 3.23/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.23/0.99    inference(negated_conjecture,[],[f18])).
% 3.23/0.99  
% 3.23/0.99  fof(f39,plain,(
% 3.23/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.23/0.99    inference(ennf_transformation,[],[f19])).
% 3.23/0.99  
% 3.23/0.99  fof(f40,plain,(
% 3.23/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.23/0.99    inference(flattening,[],[f39])).
% 3.23/0.99  
% 3.23/0.99  fof(f46,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f45,plain,(
% 3.23/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f47,plain,(
% 3.23/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.23/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f46,f45])).
% 3.23/0.99  
% 3.23/0.99  fof(f79,plain,(
% 3.23/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f14,axiom,(
% 3.23/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f20,plain,(
% 3.23/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.23/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.23/0.99  
% 3.23/0.99  fof(f68,plain,(
% 3.23/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f20])).
% 3.23/0.99  
% 3.23/0.99  fof(f73,plain,(
% 3.23/0.99    v1_funct_1(sK2)),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f75,plain,(
% 3.23/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f76,plain,(
% 3.23/0.99    v1_funct_1(sK3)),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f78,plain,(
% 3.23/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f17,axiom,(
% 3.23/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f37,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.23/0.99    inference(ennf_transformation,[],[f17])).
% 3.23/0.99  
% 3.23/0.99  fof(f38,plain,(
% 3.23/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.23/0.99    inference(flattening,[],[f37])).
% 3.23/0.99  
% 3.23/0.99  fof(f71,plain,(
% 3.23/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f38])).
% 3.23/0.99  
% 3.23/0.99  fof(f74,plain,(
% 3.23/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f77,plain,(
% 3.23/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f10,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f28,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(ennf_transformation,[],[f10])).
% 3.23/0.99  
% 3.23/0.99  fof(f61,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f28])).
% 3.23/0.99  
% 3.23/0.99  fof(f16,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f35,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.23/0.99    inference(ennf_transformation,[],[f16])).
% 3.23/0.99  
% 3.23/0.99  fof(f36,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.23/0.99    inference(flattening,[],[f35])).
% 3.23/0.99  
% 3.23/0.99  fof(f70,plain,(
% 3.23/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f36])).
% 3.23/0.99  
% 3.23/0.99  fof(f9,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f21,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.23/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.23/0.99  
% 3.23/0.99  fof(f27,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(ennf_transformation,[],[f21])).
% 3.23/0.99  
% 3.23/0.99  fof(f60,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f27])).
% 3.23/0.99  
% 3.23/0.99  fof(f12,axiom,(
% 3.23/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f31,plain,(
% 3.23/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.23/0.99    inference(ennf_transformation,[],[f12])).
% 3.23/0.99  
% 3.23/0.99  fof(f32,plain,(
% 3.23/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.23/0.99    inference(flattening,[],[f31])).
% 3.23/0.99  
% 3.23/0.99  fof(f44,plain,(
% 3.23/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.23/0.99    inference(nnf_transformation,[],[f32])).
% 3.23/0.99  
% 3.23/0.99  fof(f65,plain,(
% 3.23/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f44])).
% 3.23/0.99  
% 3.23/0.99  fof(f87,plain,(
% 3.23/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.23/0.99    inference(equality_resolution,[],[f65])).
% 3.23/0.99  
% 3.23/0.99  fof(f8,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f26,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(ennf_transformation,[],[f8])).
% 3.23/0.99  
% 3.23/0.99  fof(f59,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f26])).
% 3.23/0.99  
% 3.23/0.99  fof(f80,plain,(
% 3.23/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.23/0.99    inference(cnf_transformation,[],[f47])).
% 3.23/0.99  
% 3.23/0.99  fof(f7,axiom,(
% 3.23/0.99    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f58,plain,(
% 3.23/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f7])).
% 3.23/0.99  
% 3.23/0.99  fof(f15,axiom,(
% 3.23/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f69,plain,(
% 3.23/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f15])).
% 3.23/0.99  
% 3.23/0.99  fof(f83,plain,(
% 3.23/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.23/0.99    inference(definition_unfolding,[],[f58,f69])).
% 3.23/0.99  
% 3.23/0.99  fof(f3,axiom,(
% 3.23/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f41,plain,(
% 3.23/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/0.99    inference(nnf_transformation,[],[f3])).
% 3.23/0.99  
% 3.23/0.99  fof(f42,plain,(
% 3.23/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/0.99    inference(flattening,[],[f41])).
% 3.23/0.99  
% 3.23/0.99  fof(f51,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.23/0.99    inference(cnf_transformation,[],[f42])).
% 3.23/0.99  
% 3.23/0.99  fof(f85,plain,(
% 3.23/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.23/0.99    inference(equality_resolution,[],[f51])).
% 3.23/0.99  
% 3.23/0.99  fof(f2,axiom,(
% 3.23/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f22,plain,(
% 3.23/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f2])).
% 3.23/0.99  
% 3.23/0.99  fof(f49,plain,(
% 3.23/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f22])).
% 3.23/0.99  
% 3.23/0.99  fof(f4,axiom,(
% 3.23/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f23,plain,(
% 3.23/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f4])).
% 3.23/0.99  
% 3.23/0.99  fof(f53,plain,(
% 3.23/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f23])).
% 3.23/0.99  
% 3.23/0.99  fof(f5,axiom,(
% 3.23/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f24,plain,(
% 3.23/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f5])).
% 3.23/0.99  
% 3.23/0.99  fof(f25,plain,(
% 3.23/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.23/0.99    inference(flattening,[],[f24])).
% 3.23/0.99  
% 3.23/0.99  fof(f55,plain,(
% 3.23/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f25])).
% 3.23/0.99  
% 3.23/0.99  fof(f1,axiom,(
% 3.23/0.99    v1_xboole_0(k1_xboole_0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f48,plain,(
% 3.23/0.99    v1_xboole_0(k1_xboole_0)),
% 3.23/0.99    inference(cnf_transformation,[],[f1])).
% 3.23/0.99  
% 3.23/0.99  fof(f6,axiom,(
% 3.23/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f57,plain,(
% 3.23/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.23/0.99    inference(cnf_transformation,[],[f6])).
% 3.23/0.99  
% 3.23/0.99  fof(f81,plain,(
% 3.23/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.23/0.99    inference(definition_unfolding,[],[f57,f69])).
% 3.23/0.99  
% 3.23/0.99  cnf(c_18,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.23/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_funct_1(X3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1157,plain,
% 3.23/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.23/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.23/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.23/0.99      | v1_funct_1(X3) != iProver_top
% 3.23/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_15,plain,
% 3.23/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.23/0.99      | X3 = X2 ),
% 3.23/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_25,negated_conjecture,
% 3.23/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.23/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_443,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | X3 = X0
% 3.23/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.23/0.99      | k6_partfun1(sK0) != X3
% 3.23/0.99      | sK0 != X2
% 3.23/0.99      | sK0 != X1 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_444,plain,
% 3.23/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_20,plain,
% 3.23/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_452,plain,
% 3.23/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.23/0.99      inference(forward_subsumption_resolution,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_444,c_20]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1143,plain,
% 3.23/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.23/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4289,plain,
% 3.23/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 3.23/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.23/0.99      | v1_funct_1(sK2) != iProver_top
% 3.23/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1157,c_1143]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_31,negated_conjecture,
% 3.23/0.99      ( v1_funct_1(sK2) ),
% 3.23/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_32,plain,
% 3.23/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_29,negated_conjecture,
% 3.23/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_34,plain,
% 3.23/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_28,negated_conjecture,
% 3.23/0.99      ( v1_funct_1(sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_35,plain,
% 3.23/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_26,negated_conjecture,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_37,plain,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4881,plain,
% 3.23/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_4289,c_32,c_34,c_35,c_37]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_23,plain,
% 3.23/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.23/0.99      | ~ v1_funct_2(X3,X2,X4)
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.23/0.99      | ~ v1_funct_1(X3)
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | v2_funct_1(X0)
% 3.23/0.99      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 3.23/0.99      | k1_xboole_0 = X4 ),
% 3.23/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1153,plain,
% 3.23/0.99      ( k1_xboole_0 = X0
% 3.23/0.99      | v1_funct_2(X1,X2,X3) != iProver_top
% 3.23/0.99      | v1_funct_2(X4,X3,X0) != iProver_top
% 3.23/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.23/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.23/0.99      | v1_funct_1(X4) != iProver_top
% 3.23/0.99      | v1_funct_1(X1) != iProver_top
% 3.23/0.99      | v2_funct_1(X1) = iProver_top
% 3.23/0.99      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4907,plain,
% 3.23/0.99      ( sK0 = k1_xboole_0
% 3.23/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.23/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.23/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.23/0.99      | v1_funct_1(sK2) != iProver_top
% 3.23/0.99      | v1_funct_1(sK3) != iProver_top
% 3.23/0.99      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.23/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_4881,c_1153]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_30,negated_conjecture,
% 3.23/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.23/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_33,plain,
% 3.23/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_27,negated_conjecture,
% 3.23/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_36,plain,
% 3.23/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1152,plain,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_13,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1158,plain,
% 3.23/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.23/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3208,plain,
% 3.23/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1152,c_1158]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_21,plain,
% 3.23/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.23/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.23/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.23/0.99      | ~ v1_funct_1(X2)
% 3.23/0.99      | ~ v1_funct_1(X3)
% 3.23/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_456,plain,
% 3.23/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.23/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | ~ v1_funct_1(X3)
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.23/0.99      | k2_relset_1(X2,X1,X3) = X1
% 3.23/0.99      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.23/0.99      | sK0 != X1 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_457,plain,
% 3.23/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.23/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.23/0.99      | ~ v1_funct_1(X2)
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.23/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 3.23/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_456]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_534,plain,
% 3.23/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.23/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_funct_1(X2)
% 3.23/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.23/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.23/0.99      inference(equality_resolution_simp,[status(thm)],[c_457]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1142,plain,
% 3.23/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.23/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 3.23/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.23/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.23/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.23/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.23/0.99      | v1_funct_1(X2) != iProver_top
% 3.23/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2128,plain,
% 3.23/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.23/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.23/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.23/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.23/0.99      | v1_funct_1(sK2) != iProver_top
% 3.23/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.23/0.99      inference(equality_resolution,[status(thm)],[c_1142]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2207,plain,
% 3.23/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_2128,c_32,c_33,c_34,c_35,c_36,c_37]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3223,plain,
% 3.23/0.99      ( k2_relat_1(sK3) = sK0 ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_3208,c_2207]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_12,plain,
% 3.23/0.99      ( v5_relat_1(X0,X1)
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_16,plain,
% 3.23/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.23/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.23/0.99      | ~ v1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_327,plain,
% 3.23/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.23/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.23/0.99      | ~ v1_relat_1(X0)
% 3.23/0.99      | X0 != X1
% 3.23/0.99      | k2_relat_1(X0) != X3 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_328,plain,
% 3.23/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.23/0.99      | ~ v1_relat_1(X0) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_327]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_11,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | v1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_338,plain,
% 3.23/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.23/0.99      inference(forward_subsumption_resolution,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_328,c_11]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_24,negated_conjecture,
% 3.23/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.23/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_353,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.23/0.99      | ~ v2_funct_1(sK2)
% 3.23/0.99      | k2_relat_1(X0) != sK0
% 3.23/0.99      | sK3 != X0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_338,c_24]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_354,plain,
% 3.23/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.23/0.99      | ~ v2_funct_1(sK2)
% 3.23/0.99      | k2_relat_1(sK3) != sK0 ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_701,plain,
% 3.23/0.99      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 3.23/0.99      inference(splitting,
% 3.23/0.99                [splitting(split),new_symbols(definition,[])],
% 3.23/0.99                [c_354]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1145,plain,
% 3.23/0.99      ( k2_relat_1(sK3) != sK0
% 3.23/0.99      | v2_funct_1(sK2) != iProver_top
% 3.23/0.99      | sP0_iProver_split = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3302,plain,
% 3.23/0.99      ( sK0 != sK0
% 3.23/0.99      | v2_funct_1(sK2) != iProver_top
% 3.23/0.99      | sP0_iProver_split = iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_3223,c_1145]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3303,plain,
% 3.23/0.99      ( v2_funct_1(sK2) != iProver_top
% 3.23/0.99      | sP0_iProver_split = iProver_top ),
% 3.23/0.99      inference(equality_resolution_simp,[status(thm)],[c_3302]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_700,plain,
% 3.23/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.23/0.99      | ~ sP0_iProver_split ),
% 3.23/0.99      inference(splitting,
% 3.23/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.23/0.99                [c_354]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1146,plain,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.23/0.99      | sP0_iProver_split != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3301,plain,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.23/0.99      | sP0_iProver_split != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_3223,c_1146]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3471,plain,
% 3.23/0.99      ( sP0_iProver_split != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1152,c_3301]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6060,plain,
% 3.23/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_4907,c_32,c_33,c_34,c_35,c_36,c_37,c_3303,c_3471]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6061,plain,
% 3.23/0.99      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.23/0.99      inference(renaming,[status(thm)],[c_6060]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_10,plain,
% 3.23/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.23/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1160,plain,
% 3.23/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6066,plain,
% 3.23/0.99      ( sK0 = k1_xboole_0 ),
% 3.23/0.99      inference(forward_subsumption_resolution,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_6061,c_1160]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1149,plain,
% 3.23/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6077,plain,
% 3.23/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_6066,c_1149]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3,plain,
% 3.23/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6085,plain,
% 3.23/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_6077,c_3]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_712,plain,
% 3.23/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.23/0.99      theory(equality) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2835,plain,
% 3.23/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_712]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2836,plain,
% 3.23/0.99      ( sK2 != X0
% 3.23/0.99      | v2_funct_1(X0) != iProver_top
% 3.23/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_2835]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2838,plain,
% 3.23/0.99      ( sK2 != k1_xboole_0
% 3.23/0.99      | v2_funct_1(sK2) = iProver_top
% 3.23/0.99      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_2836]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1,plain,
% 3.23/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2700,plain,
% 3.23/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2701,plain,
% 3.23/0.99      ( sK2 = X0
% 3.23/0.99      | v1_xboole_0(X0) != iProver_top
% 3.23/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_2700]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2703,plain,
% 3.23/0.99      ( sK2 = k1_xboole_0
% 3.23/0.99      | v1_xboole_0(sK2) != iProver_top
% 3.23/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_2701]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.23/0.99      | ~ v1_xboole_0(X1)
% 3.23/0.99      | v1_xboole_0(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2466,plain,
% 3.23/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.23/0.99      | ~ v1_xboole_0(X0)
% 3.23/0.99      | v1_xboole_0(sK2) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2467,plain,
% 3.23/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.23/0.99      | v1_xboole_0(X0) != iProver_top
% 3.23/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_2466]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2469,plain,
% 3.23/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.23/0.99      | v1_xboole_0(sK2) = iProver_top
% 3.23/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_2467]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6,plain,
% 3.23/0.99      ( ~ v1_relat_1(X0)
% 3.23/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.23/0.99      | k1_xboole_0 = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1672,plain,
% 3.23/0.99      ( ~ v1_relat_1(k6_partfun1(X0))
% 3.23/0.99      | k2_relat_1(k6_partfun1(X0)) != k1_xboole_0
% 3.23/0.99      | k1_xboole_0 = k6_partfun1(X0) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1676,plain,
% 3.23/0.99      ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
% 3.23/0.99      | k2_relat_1(k6_partfun1(k1_xboole_0)) != k1_xboole_0
% 3.23/0.99      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1672]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1415,plain,
% 3.23/0.99      ( v2_funct_1(X0)
% 3.23/0.99      | ~ v2_funct_1(k6_partfun1(X1))
% 3.23/0.99      | X0 != k6_partfun1(X1) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_712]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1416,plain,
% 3.23/0.99      ( X0 != k6_partfun1(X1)
% 3.23/0.99      | v2_funct_1(X0) = iProver_top
% 3.23/0.99      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1415]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1418,plain,
% 3.23/0.99      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.23/0.99      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.23/0.99      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1416]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1400,plain,
% 3.23/0.99      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.23/0.99      | v1_relat_1(k6_partfun1(X0)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1402,plain,
% 3.23/0.99      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.23/0.99      | v1_relat_1(k6_partfun1(k1_xboole_0)) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_1400]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_0,plain,
% 3.23/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_96,plain,
% 3.23/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_8,plain,
% 3.23/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_83,plain,
% 3.23/0.99      ( k2_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_79,plain,
% 3.23/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_81,plain,
% 3.23/0.99      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_79]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_50,plain,
% 3.23/0.99      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(contradiction,plain,
% 3.23/0.99      ( $false ),
% 3.23/0.99      inference(minisat,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_6085,c_3471,c_3303,c_2838,c_2703,c_2469,c_1676,c_1418,
% 3.23/0.99                 c_1402,c_96,c_83,c_81,c_50]) ).
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  ------                               Statistics
% 3.23/0.99  
% 3.23/0.99  ------ General
% 3.23/0.99  
% 3.23/0.99  abstr_ref_over_cycles:                  0
% 3.23/0.99  abstr_ref_under_cycles:                 0
% 3.23/0.99  gc_basic_clause_elim:                   0
% 3.23/0.99  forced_gc_time:                         0
% 3.23/0.99  parsing_time:                           0.009
% 3.23/0.99  unif_index_cands_time:                  0.
% 3.23/0.99  unif_index_add_time:                    0.
% 3.23/0.99  orderings_time:                         0.
% 3.23/0.99  out_proof_time:                         0.016
% 3.23/0.99  total_time:                             0.296
% 3.23/0.99  num_of_symbols:                         53
% 3.23/0.99  num_of_terms:                           7509
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing
% 3.23/0.99  
% 3.23/0.99  num_of_splits:                          1
% 3.23/0.99  num_of_split_atoms:                     1
% 3.23/0.99  num_of_reused_defs:                     0
% 3.23/0.99  num_eq_ax_congr_red:                    11
% 3.23/0.99  num_of_sem_filtered_clauses:            1
% 3.23/0.99  num_of_subtypes:                        0
% 3.23/0.99  monotx_restored_types:                  0
% 3.23/0.99  sat_num_of_epr_types:                   0
% 3.23/0.99  sat_num_of_non_cyclic_types:            0
% 3.23/0.99  sat_guarded_non_collapsed_types:        0
% 3.23/0.99  num_pure_diseq_elim:                    0
% 3.23/0.99  simp_replaced_by:                       0
% 3.23/0.99  res_preprocessed:                       147
% 3.23/0.99  prep_upred:                             0
% 3.23/0.99  prep_unflattend:                        17
% 3.23/0.99  smt_new_axioms:                         0
% 3.23/0.99  pred_elim_cands:                        6
% 3.23/0.99  pred_elim:                              3
% 3.23/0.99  pred_elim_cl:                           4
% 3.23/0.99  pred_elim_cycles:                       6
% 3.23/0.99  merged_defs:                            0
% 3.23/0.99  merged_defs_ncl:                        0
% 3.23/0.99  bin_hyper_res:                          0
% 3.23/0.99  prep_cycles:                            4
% 3.23/0.99  pred_elim_time:                         0.006
% 3.23/0.99  splitting_time:                         0.
% 3.23/0.99  sem_filter_time:                        0.
% 3.23/0.99  monotx_time:                            0.001
% 3.23/0.99  subtype_inf_time:                       0.
% 3.23/0.99  
% 3.23/0.99  ------ Problem properties
% 3.23/0.99  
% 3.23/0.99  clauses:                                29
% 3.23/0.99  conjectures:                            6
% 3.23/0.99  epr:                                    6
% 3.23/0.99  horn:                                   27
% 3.23/0.99  ground:                                 9
% 3.23/0.99  unary:                                  13
% 3.23/0.99  binary:                                 4
% 3.23/0.99  lits:                                   82
% 3.23/0.99  lits_eq:                                20
% 3.23/0.99  fd_pure:                                0
% 3.23/0.99  fd_pseudo:                              0
% 3.23/0.99  fd_cond:                                4
% 3.23/0.99  fd_pseudo_cond:                         1
% 3.23/0.99  ac_symbols:                             0
% 3.23/0.99  
% 3.23/0.99  ------ Propositional Solver
% 3.23/0.99  
% 3.23/0.99  prop_solver_calls:                      27
% 3.23/0.99  prop_fast_solver_calls:                 1059
% 3.23/0.99  smt_solver_calls:                       0
% 3.23/0.99  smt_fast_solver_calls:                  0
% 3.23/0.99  prop_num_of_clauses:                    2618
% 3.23/0.99  prop_preprocess_simplified:             8035
% 3.23/0.99  prop_fo_subsumed:                       25
% 3.23/0.99  prop_solver_time:                       0.
% 3.23/0.99  smt_solver_time:                        0.
% 3.23/0.99  smt_fast_solver_time:                   0.
% 3.23/0.99  prop_fast_solver_time:                  0.
% 3.23/0.99  prop_unsat_core_time:                   0.
% 3.23/0.99  
% 3.23/0.99  ------ QBF
% 3.23/0.99  
% 3.23/0.99  qbf_q_res:                              0
% 3.23/0.99  qbf_num_tautologies:                    0
% 3.23/0.99  qbf_prep_cycles:                        0
% 3.23/0.99  
% 3.23/0.99  ------ BMC1
% 3.23/0.99  
% 3.23/0.99  bmc1_current_bound:                     -1
% 3.23/0.99  bmc1_last_solved_bound:                 -1
% 3.23/0.99  bmc1_unsat_core_size:                   -1
% 3.23/0.99  bmc1_unsat_core_parents_size:           -1
% 3.23/0.99  bmc1_merge_next_fun:                    0
% 3.23/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation
% 3.23/0.99  
% 3.23/0.99  inst_num_of_clauses:                    853
% 3.23/0.99  inst_num_in_passive:                    415
% 3.23/0.99  inst_num_in_active:                     325
% 3.23/0.99  inst_num_in_unprocessed:                113
% 3.23/0.99  inst_num_of_loops:                      330
% 3.23/0.99  inst_num_of_learning_restarts:          0
% 3.23/0.99  inst_num_moves_active_passive:          4
% 3.23/0.99  inst_lit_activity:                      0
% 3.23/0.99  inst_lit_activity_moves:                0
% 3.23/0.99  inst_num_tautologies:                   0
% 3.23/0.99  inst_num_prop_implied:                  0
% 3.23/0.99  inst_num_existing_simplified:           0
% 3.23/0.99  inst_num_eq_res_simplified:             0
% 3.23/0.99  inst_num_child_elim:                    0
% 3.23/0.99  inst_num_of_dismatching_blockings:      33
% 3.23/0.99  inst_num_of_non_proper_insts:           522
% 3.23/0.99  inst_num_of_duplicates:                 0
% 3.23/0.99  inst_inst_num_from_inst_to_res:         0
% 3.23/0.99  inst_dismatching_checking_time:         0.
% 3.23/0.99  
% 3.23/0.99  ------ Resolution
% 3.23/0.99  
% 3.23/0.99  res_num_of_clauses:                     0
% 3.23/0.99  res_num_in_passive:                     0
% 3.23/0.99  res_num_in_active:                      0
% 3.23/0.99  res_num_of_loops:                       151
% 3.23/0.99  res_forward_subset_subsumed:            14
% 3.23/0.99  res_backward_subset_subsumed:           0
% 3.23/0.99  res_forward_subsumed:                   0
% 3.23/0.99  res_backward_subsumed:                  0
% 3.23/0.99  res_forward_subsumption_resolution:     4
% 3.23/0.99  res_backward_subsumption_resolution:    0
% 3.23/0.99  res_clause_to_clause_subsumption:       142
% 3.23/0.99  res_orphan_elimination:                 0
% 3.23/0.99  res_tautology_del:                      25
% 3.23/0.99  res_num_eq_res_simplified:              1
% 3.23/0.99  res_num_sel_changes:                    0
% 3.23/0.99  res_moves_from_active_to_pass:          0
% 3.23/0.99  
% 3.23/0.99  ------ Superposition
% 3.23/0.99  
% 3.23/0.99  sup_time_total:                         0.
% 3.23/0.99  sup_time_generating:                    0.
% 3.23/0.99  sup_time_sim_full:                      0.
% 3.23/0.99  sup_time_sim_immed:                     0.
% 3.23/0.99  
% 3.23/0.99  sup_num_of_clauses:                     63
% 3.23/0.99  sup_num_in_active:                      45
% 3.23/0.99  sup_num_in_passive:                     18
% 3.23/0.99  sup_num_of_loops:                       64
% 3.23/0.99  sup_fw_superposition:                   31
% 3.23/0.99  sup_bw_superposition:                   29
% 3.23/0.99  sup_immediate_simplified:               21
% 3.23/0.99  sup_given_eliminated:                   1
% 3.23/0.99  comparisons_done:                       0
% 3.23/0.99  comparisons_avoided:                    0
% 3.23/0.99  
% 3.23/0.99  ------ Simplifications
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  sim_fw_subset_subsumed:                 1
% 3.23/0.99  sim_bw_subset_subsumed:                 0
% 3.23/0.99  sim_fw_subsumed:                        4
% 3.23/0.99  sim_bw_subsumed:                        1
% 3.23/0.99  sim_fw_subsumption_res:                 1
% 3.23/0.99  sim_bw_subsumption_res:                 0
% 3.23/0.99  sim_tautology_del:                      3
% 3.23/0.99  sim_eq_tautology_del:                   4
% 3.23/0.99  sim_eq_res_simp:                        2
% 3.23/0.99  sim_fw_demodulated:                     9
% 3.23/0.99  sim_bw_demodulated:                     22
% 3.23/0.99  sim_light_normalised:                   11
% 3.23/0.99  sim_joinable_taut:                      0
% 3.23/0.99  sim_joinable_simp:                      0
% 3.23/0.99  sim_ac_normalised:                      0
% 3.23/0.99  sim_smt_subsumption:                    0
% 3.23/0.99  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:49 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  169 (1684 expanded)
%              Number of clauses        :   92 ( 451 expanded)
%              Number of leaves         :   20 ( 414 expanded)
%              Depth                    :   23
%              Number of atoms          :  621 (11066 expanded)
%              Number of equality atoms :  188 ( 793 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f85,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f80,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_438,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_446,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_438,c_20])).

cnf(c_1120,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1610,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_1714,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1120,c_31,c_29,c_28,c_26,c_446,c_1610])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1131,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4675,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1131])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1583,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1584,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1853,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1854,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1853])).

cnf(c_1130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1136,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2279,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1130,c_1136])).

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

cnf(c_450,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_451,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_451])).

cnf(c_1119,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_1787,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1119,c_1714])).

cnf(c_1799,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1787])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_402,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X1 != X6
    | X1 != X5
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != X4
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_403,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k1_partfun1(X1,X2,X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_425,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_403,c_18])).

cnf(c_1461,plain,
    ( ~ v1_funct_2(X0,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_1508,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_1860,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1799,c_31,c_30,c_29,c_28,c_27,c_26,c_446,c_1508,c_1610])).

cnf(c_2294,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2279,c_1860])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_24,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_356,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_357,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X2
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_357])).

cnf(c_378,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_665,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_378])).

cnf(c_1122,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_2665,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2294,c_1122])).

cnf(c_2671,plain,
    ( v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2665])).

cnf(c_664,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_378])).

cnf(c_1123,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_2666,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2294,c_1123])).

cnf(c_2685,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_2666])).

cnf(c_4907,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4675,c_32,c_33,c_34,c_35,c_36,c_37,c_1584,c_1854,c_2671,c_2685])).

cnf(c_4908,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4907])).

cnf(c_11,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1137,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4913,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4908,c_1137])).

cnf(c_1127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3961,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1141])).

cnf(c_1586,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1587,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_1856,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1857,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1856])).

cnf(c_8,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_175,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_7])).

cnf(c_2538,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_2539,plain,
    ( v2_funct_1(sK2) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2538])).

cnf(c_4176,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3961,c_34,c_37,c_1584,c_1587,c_1854,c_1857,c_2539,c_2671,c_2685])).

cnf(c_4915,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4913,c_4176])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4967,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4915,c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4967,c_94])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:49:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 3.17/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/1.00  
% 3.17/1.00  ------  iProver source info
% 3.17/1.00  
% 3.17/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.17/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/1.00  git: non_committed_changes: false
% 3.17/1.00  git: last_make_outside_of_git: false
% 3.17/1.00  
% 3.17/1.00  ------ 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options
% 3.17/1.00  
% 3.17/1.00  --out_options                           all
% 3.17/1.00  --tptp_safe_out                         true
% 3.17/1.00  --problem_path                          ""
% 3.17/1.00  --include_path                          ""
% 3.17/1.00  --clausifier                            res/vclausify_rel
% 3.17/1.00  --clausifier_options                    --mode clausify
% 3.17/1.00  --stdin                                 false
% 3.17/1.00  --stats_out                             all
% 3.17/1.00  
% 3.17/1.00  ------ General Options
% 3.17/1.00  
% 3.17/1.00  --fof                                   false
% 3.17/1.00  --time_out_real                         305.
% 3.17/1.00  --time_out_virtual                      -1.
% 3.17/1.00  --symbol_type_check                     false
% 3.17/1.00  --clausify_out                          false
% 3.17/1.00  --sig_cnt_out                           false
% 3.17/1.00  --trig_cnt_out                          false
% 3.17/1.00  --trig_cnt_out_tolerance                1.
% 3.17/1.00  --trig_cnt_out_sk_spl                   false
% 3.17/1.00  --abstr_cl_out                          false
% 3.17/1.00  
% 3.17/1.00  ------ Global Options
% 3.17/1.00  
% 3.17/1.00  --schedule                              default
% 3.17/1.00  --add_important_lit                     false
% 3.17/1.00  --prop_solver_per_cl                    1000
% 3.17/1.00  --min_unsat_core                        false
% 3.17/1.00  --soft_assumptions                      false
% 3.17/1.00  --soft_lemma_size                       3
% 3.17/1.00  --prop_impl_unit_size                   0
% 3.17/1.00  --prop_impl_unit                        []
% 3.17/1.00  --share_sel_clauses                     true
% 3.17/1.00  --reset_solvers                         false
% 3.17/1.00  --bc_imp_inh                            [conj_cone]
% 3.17/1.00  --conj_cone_tolerance                   3.
% 3.17/1.00  --extra_neg_conj                        none
% 3.17/1.00  --large_theory_mode                     true
% 3.17/1.00  --prolific_symb_bound                   200
% 3.17/1.00  --lt_threshold                          2000
% 3.17/1.00  --clause_weak_htbl                      true
% 3.17/1.00  --gc_record_bc_elim                     false
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing Options
% 3.17/1.00  
% 3.17/1.00  --preprocessing_flag                    true
% 3.17/1.00  --time_out_prep_mult                    0.1
% 3.17/1.00  --splitting_mode                        input
% 3.17/1.00  --splitting_grd                         true
% 3.17/1.00  --splitting_cvd                         false
% 3.17/1.00  --splitting_cvd_svl                     false
% 3.17/1.00  --splitting_nvd                         32
% 3.17/1.00  --sub_typing                            true
% 3.17/1.00  --prep_gs_sim                           true
% 3.17/1.00  --prep_unflatten                        true
% 3.17/1.00  --prep_res_sim                          true
% 3.17/1.00  --prep_upred                            true
% 3.17/1.00  --prep_sem_filter                       exhaustive
% 3.17/1.00  --prep_sem_filter_out                   false
% 3.17/1.00  --pred_elim                             true
% 3.17/1.00  --res_sim_input                         true
% 3.17/1.00  --eq_ax_congr_red                       true
% 3.17/1.00  --pure_diseq_elim                       true
% 3.17/1.00  --brand_transform                       false
% 3.17/1.00  --non_eq_to_eq                          false
% 3.17/1.00  --prep_def_merge                        true
% 3.17/1.00  --prep_def_merge_prop_impl              false
% 3.17/1.00  --prep_def_merge_mbd                    true
% 3.17/1.00  --prep_def_merge_tr_red                 false
% 3.17/1.00  --prep_def_merge_tr_cl                  false
% 3.17/1.00  --smt_preprocessing                     true
% 3.17/1.00  --smt_ac_axioms                         fast
% 3.17/1.00  --preprocessed_out                      false
% 3.17/1.00  --preprocessed_stats                    false
% 3.17/1.00  
% 3.17/1.00  ------ Abstraction refinement Options
% 3.17/1.00  
% 3.17/1.00  --abstr_ref                             []
% 3.17/1.00  --abstr_ref_prep                        false
% 3.17/1.00  --abstr_ref_until_sat                   false
% 3.17/1.00  --abstr_ref_sig_restrict                funpre
% 3.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.00  --abstr_ref_under                       []
% 3.17/1.00  
% 3.17/1.00  ------ SAT Options
% 3.17/1.00  
% 3.17/1.00  --sat_mode                              false
% 3.17/1.00  --sat_fm_restart_options                ""
% 3.17/1.00  --sat_gr_def                            false
% 3.17/1.00  --sat_epr_types                         true
% 3.17/1.00  --sat_non_cyclic_types                  false
% 3.17/1.00  --sat_finite_models                     false
% 3.17/1.00  --sat_fm_lemmas                         false
% 3.17/1.00  --sat_fm_prep                           false
% 3.17/1.00  --sat_fm_uc_incr                        true
% 3.17/1.00  --sat_out_model                         small
% 3.17/1.00  --sat_out_clauses                       false
% 3.17/1.00  
% 3.17/1.00  ------ QBF Options
% 3.17/1.00  
% 3.17/1.00  --qbf_mode                              false
% 3.17/1.00  --qbf_elim_univ                         false
% 3.17/1.00  --qbf_dom_inst                          none
% 3.17/1.00  --qbf_dom_pre_inst                      false
% 3.17/1.00  --qbf_sk_in                             false
% 3.17/1.00  --qbf_pred_elim                         true
% 3.17/1.00  --qbf_split                             512
% 3.17/1.00  
% 3.17/1.00  ------ BMC1 Options
% 3.17/1.00  
% 3.17/1.00  --bmc1_incremental                      false
% 3.17/1.00  --bmc1_axioms                           reachable_all
% 3.17/1.00  --bmc1_min_bound                        0
% 3.17/1.00  --bmc1_max_bound                        -1
% 3.17/1.00  --bmc1_max_bound_default                -1
% 3.17/1.00  --bmc1_symbol_reachability              true
% 3.17/1.00  --bmc1_property_lemmas                  false
% 3.17/1.00  --bmc1_k_induction                      false
% 3.17/1.00  --bmc1_non_equiv_states                 false
% 3.17/1.00  --bmc1_deadlock                         false
% 3.17/1.00  --bmc1_ucm                              false
% 3.17/1.00  --bmc1_add_unsat_core                   none
% 3.17/1.00  --bmc1_unsat_core_children              false
% 3.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.00  --bmc1_out_stat                         full
% 3.17/1.00  --bmc1_ground_init                      false
% 3.17/1.00  --bmc1_pre_inst_next_state              false
% 3.17/1.00  --bmc1_pre_inst_state                   false
% 3.17/1.00  --bmc1_pre_inst_reach_state             false
% 3.17/1.00  --bmc1_out_unsat_core                   false
% 3.17/1.00  --bmc1_aig_witness_out                  false
% 3.17/1.00  --bmc1_verbose                          false
% 3.17/1.00  --bmc1_dump_clauses_tptp                false
% 3.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.00  --bmc1_dump_file                        -
% 3.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.00  --bmc1_ucm_extend_mode                  1
% 3.17/1.00  --bmc1_ucm_init_mode                    2
% 3.17/1.00  --bmc1_ucm_cone_mode                    none
% 3.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.00  --bmc1_ucm_relax_model                  4
% 3.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.00  --bmc1_ucm_layered_model                none
% 3.17/1.00  --bmc1_ucm_max_lemma_size               10
% 3.17/1.00  
% 3.17/1.00  ------ AIG Options
% 3.17/1.00  
% 3.17/1.00  --aig_mode                              false
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation Options
% 3.17/1.00  
% 3.17/1.00  --instantiation_flag                    true
% 3.17/1.00  --inst_sos_flag                         false
% 3.17/1.00  --inst_sos_phase                        true
% 3.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel_side                     num_symb
% 3.17/1.00  --inst_solver_per_active                1400
% 3.17/1.00  --inst_solver_calls_frac                1.
% 3.17/1.00  --inst_passive_queue_type               priority_queues
% 3.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.00  --inst_passive_queues_freq              [25;2]
% 3.17/1.00  --inst_dismatching                      true
% 3.17/1.00  --inst_eager_unprocessed_to_passive     true
% 3.17/1.00  --inst_prop_sim_given                   true
% 3.17/1.00  --inst_prop_sim_new                     false
% 3.17/1.00  --inst_subs_new                         false
% 3.17/1.00  --inst_eq_res_simp                      false
% 3.17/1.00  --inst_subs_given                       false
% 3.17/1.00  --inst_orphan_elimination               true
% 3.17/1.00  --inst_learning_loop_flag               true
% 3.17/1.00  --inst_learning_start                   3000
% 3.17/1.00  --inst_learning_factor                  2
% 3.17/1.00  --inst_start_prop_sim_after_learn       3
% 3.17/1.00  --inst_sel_renew                        solver
% 3.17/1.00  --inst_lit_activity_flag                true
% 3.17/1.00  --inst_restr_to_given                   false
% 3.17/1.00  --inst_activity_threshold               500
% 3.17/1.00  --inst_out_proof                        true
% 3.17/1.00  
% 3.17/1.00  ------ Resolution Options
% 3.17/1.00  
% 3.17/1.00  --resolution_flag                       true
% 3.17/1.00  --res_lit_sel                           adaptive
% 3.17/1.00  --res_lit_sel_side                      none
% 3.17/1.00  --res_ordering                          kbo
% 3.17/1.00  --res_to_prop_solver                    active
% 3.17/1.00  --res_prop_simpl_new                    false
% 3.17/1.00  --res_prop_simpl_given                  true
% 3.17/1.00  --res_passive_queue_type                priority_queues
% 3.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.00  --res_passive_queues_freq               [15;5]
% 3.17/1.00  --res_forward_subs                      full
% 3.17/1.00  --res_backward_subs                     full
% 3.17/1.00  --res_forward_subs_resolution           true
% 3.17/1.00  --res_backward_subs_resolution          true
% 3.17/1.00  --res_orphan_elimination                true
% 3.17/1.00  --res_time_limit                        2.
% 3.17/1.00  --res_out_proof                         true
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Options
% 3.17/1.00  
% 3.17/1.00  --superposition_flag                    true
% 3.17/1.00  --sup_passive_queue_type                priority_queues
% 3.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.00  --demod_completeness_check              fast
% 3.17/1.00  --demod_use_ground                      true
% 3.17/1.00  --sup_to_prop_solver                    passive
% 3.17/1.00  --sup_prop_simpl_new                    true
% 3.17/1.00  --sup_prop_simpl_given                  true
% 3.17/1.00  --sup_fun_splitting                     false
% 3.17/1.00  --sup_smt_interval                      50000
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Simplification Setup
% 3.17/1.00  
% 3.17/1.00  --sup_indices_passive                   []
% 3.17/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_full_bw                           [BwDemod]
% 3.17/1.00  --sup_immed_triv                        [TrivRules]
% 3.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_immed_bw_main                     []
% 3.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  
% 3.17/1.00  ------ Combination Options
% 3.17/1.00  
% 3.17/1.00  --comb_res_mult                         3
% 3.17/1.00  --comb_sup_mult                         2
% 3.17/1.00  --comb_inst_mult                        10
% 3.17/1.00  
% 3.17/1.00  ------ Debug Options
% 3.17/1.00  
% 3.17/1.00  --dbg_backtrace                         false
% 3.17/1.00  --dbg_dump_prop_clauses                 false
% 3.17/1.00  --dbg_dump_prop_clauses_file            -
% 3.17/1.00  --dbg_out_stat                          false
% 3.17/1.00  ------ Parsing...
% 3.17/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/1.00  ------ Proving...
% 3.17/1.00  ------ Problem Properties 
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  clauses                                 27
% 3.17/1.00  conjectures                             6
% 3.17/1.00  EPR                                     7
% 3.17/1.00  Horn                                    25
% 3.17/1.00  unary                                   12
% 3.17/1.00  binary                                  4
% 3.17/1.00  lits                                    79
% 3.17/1.00  lits eq                                 13
% 3.17/1.00  fd_pure                                 0
% 3.17/1.00  fd_pseudo                               0
% 3.17/1.00  fd_cond                                 2
% 3.17/1.00  fd_pseudo_cond                          0
% 3.17/1.00  AC symbols                              0
% 3.17/1.00  
% 3.17/1.00  ------ Schedule dynamic 5 is on 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  ------ 
% 3.17/1.00  Current options:
% 3.17/1.00  ------ 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options
% 3.17/1.00  
% 3.17/1.00  --out_options                           all
% 3.17/1.00  --tptp_safe_out                         true
% 3.17/1.00  --problem_path                          ""
% 3.17/1.00  --include_path                          ""
% 3.17/1.00  --clausifier                            res/vclausify_rel
% 3.17/1.00  --clausifier_options                    --mode clausify
% 3.17/1.00  --stdin                                 false
% 3.17/1.00  --stats_out                             all
% 3.17/1.00  
% 3.17/1.00  ------ General Options
% 3.17/1.00  
% 3.17/1.00  --fof                                   false
% 3.17/1.00  --time_out_real                         305.
% 3.17/1.00  --time_out_virtual                      -1.
% 3.17/1.00  --symbol_type_check                     false
% 3.17/1.00  --clausify_out                          false
% 3.17/1.00  --sig_cnt_out                           false
% 3.17/1.00  --trig_cnt_out                          false
% 3.17/1.00  --trig_cnt_out_tolerance                1.
% 3.17/1.00  --trig_cnt_out_sk_spl                   false
% 3.17/1.00  --abstr_cl_out                          false
% 3.17/1.00  
% 3.17/1.00  ------ Global Options
% 3.17/1.00  
% 3.17/1.00  --schedule                              default
% 3.17/1.00  --add_important_lit                     false
% 3.17/1.00  --prop_solver_per_cl                    1000
% 3.17/1.00  --min_unsat_core                        false
% 3.17/1.00  --soft_assumptions                      false
% 3.17/1.00  --soft_lemma_size                       3
% 3.17/1.00  --prop_impl_unit_size                   0
% 3.17/1.00  --prop_impl_unit                        []
% 3.17/1.00  --share_sel_clauses                     true
% 3.17/1.00  --reset_solvers                         false
% 3.17/1.00  --bc_imp_inh                            [conj_cone]
% 3.17/1.00  --conj_cone_tolerance                   3.
% 3.17/1.00  --extra_neg_conj                        none
% 3.17/1.00  --large_theory_mode                     true
% 3.17/1.00  --prolific_symb_bound                   200
% 3.17/1.00  --lt_threshold                          2000
% 3.17/1.00  --clause_weak_htbl                      true
% 3.17/1.00  --gc_record_bc_elim                     false
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing Options
% 3.17/1.00  
% 3.17/1.00  --preprocessing_flag                    true
% 3.17/1.00  --time_out_prep_mult                    0.1
% 3.17/1.00  --splitting_mode                        input
% 3.17/1.00  --splitting_grd                         true
% 3.17/1.00  --splitting_cvd                         false
% 3.17/1.00  --splitting_cvd_svl                     false
% 3.17/1.00  --splitting_nvd                         32
% 3.17/1.00  --sub_typing                            true
% 3.17/1.00  --prep_gs_sim                           true
% 3.17/1.00  --prep_unflatten                        true
% 3.17/1.00  --prep_res_sim                          true
% 3.17/1.00  --prep_upred                            true
% 3.17/1.00  --prep_sem_filter                       exhaustive
% 3.17/1.00  --prep_sem_filter_out                   false
% 3.17/1.00  --pred_elim                             true
% 3.17/1.00  --res_sim_input                         true
% 3.17/1.00  --eq_ax_congr_red                       true
% 3.17/1.00  --pure_diseq_elim                       true
% 3.17/1.00  --brand_transform                       false
% 3.17/1.00  --non_eq_to_eq                          false
% 3.17/1.00  --prep_def_merge                        true
% 3.17/1.00  --prep_def_merge_prop_impl              false
% 3.17/1.00  --prep_def_merge_mbd                    true
% 3.17/1.00  --prep_def_merge_tr_red                 false
% 3.17/1.00  --prep_def_merge_tr_cl                  false
% 3.17/1.00  --smt_preprocessing                     true
% 3.17/1.00  --smt_ac_axioms                         fast
% 3.17/1.00  --preprocessed_out                      false
% 3.17/1.00  --preprocessed_stats                    false
% 3.17/1.00  
% 3.17/1.00  ------ Abstraction refinement Options
% 3.17/1.00  
% 3.17/1.00  --abstr_ref                             []
% 3.17/1.00  --abstr_ref_prep                        false
% 3.17/1.00  --abstr_ref_until_sat                   false
% 3.17/1.00  --abstr_ref_sig_restrict                funpre
% 3.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.00  --abstr_ref_under                       []
% 3.17/1.00  
% 3.17/1.00  ------ SAT Options
% 3.17/1.00  
% 3.17/1.00  --sat_mode                              false
% 3.17/1.00  --sat_fm_restart_options                ""
% 3.17/1.00  --sat_gr_def                            false
% 3.17/1.00  --sat_epr_types                         true
% 3.17/1.00  --sat_non_cyclic_types                  false
% 3.17/1.00  --sat_finite_models                     false
% 3.17/1.00  --sat_fm_lemmas                         false
% 3.17/1.00  --sat_fm_prep                           false
% 3.17/1.00  --sat_fm_uc_incr                        true
% 3.17/1.00  --sat_out_model                         small
% 3.17/1.00  --sat_out_clauses                       false
% 3.17/1.00  
% 3.17/1.00  ------ QBF Options
% 3.17/1.00  
% 3.17/1.00  --qbf_mode                              false
% 3.17/1.00  --qbf_elim_univ                         false
% 3.17/1.00  --qbf_dom_inst                          none
% 3.17/1.00  --qbf_dom_pre_inst                      false
% 3.17/1.00  --qbf_sk_in                             false
% 3.17/1.00  --qbf_pred_elim                         true
% 3.17/1.00  --qbf_split                             512
% 3.17/1.00  
% 3.17/1.00  ------ BMC1 Options
% 3.17/1.00  
% 3.17/1.00  --bmc1_incremental                      false
% 3.17/1.00  --bmc1_axioms                           reachable_all
% 3.17/1.00  --bmc1_min_bound                        0
% 3.17/1.00  --bmc1_max_bound                        -1
% 3.17/1.00  --bmc1_max_bound_default                -1
% 3.17/1.00  --bmc1_symbol_reachability              true
% 3.17/1.00  --bmc1_property_lemmas                  false
% 3.17/1.00  --bmc1_k_induction                      false
% 3.17/1.00  --bmc1_non_equiv_states                 false
% 3.17/1.00  --bmc1_deadlock                         false
% 3.17/1.00  --bmc1_ucm                              false
% 3.17/1.00  --bmc1_add_unsat_core                   none
% 3.17/1.00  --bmc1_unsat_core_children              false
% 3.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.00  --bmc1_out_stat                         full
% 3.17/1.00  --bmc1_ground_init                      false
% 3.17/1.00  --bmc1_pre_inst_next_state              false
% 3.17/1.00  --bmc1_pre_inst_state                   false
% 3.17/1.00  --bmc1_pre_inst_reach_state             false
% 3.17/1.00  --bmc1_out_unsat_core                   false
% 3.17/1.00  --bmc1_aig_witness_out                  false
% 3.17/1.00  --bmc1_verbose                          false
% 3.17/1.00  --bmc1_dump_clauses_tptp                false
% 3.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.00  --bmc1_dump_file                        -
% 3.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.00  --bmc1_ucm_extend_mode                  1
% 3.17/1.00  --bmc1_ucm_init_mode                    2
% 3.17/1.00  --bmc1_ucm_cone_mode                    none
% 3.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.00  --bmc1_ucm_relax_model                  4
% 3.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.00  --bmc1_ucm_layered_model                none
% 3.17/1.00  --bmc1_ucm_max_lemma_size               10
% 3.17/1.00  
% 3.17/1.00  ------ AIG Options
% 3.17/1.00  
% 3.17/1.00  --aig_mode                              false
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation Options
% 3.17/1.00  
% 3.17/1.00  --instantiation_flag                    true
% 3.17/1.00  --inst_sos_flag                         false
% 3.17/1.00  --inst_sos_phase                        true
% 3.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel_side                     none
% 3.17/1.00  --inst_solver_per_active                1400
% 3.17/1.00  --inst_solver_calls_frac                1.
% 3.17/1.00  --inst_passive_queue_type               priority_queues
% 3.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.00  --inst_passive_queues_freq              [25;2]
% 3.17/1.00  --inst_dismatching                      true
% 3.17/1.00  --inst_eager_unprocessed_to_passive     true
% 3.17/1.00  --inst_prop_sim_given                   true
% 3.17/1.00  --inst_prop_sim_new                     false
% 3.17/1.00  --inst_subs_new                         false
% 3.17/1.00  --inst_eq_res_simp                      false
% 3.17/1.00  --inst_subs_given                       false
% 3.17/1.00  --inst_orphan_elimination               true
% 3.17/1.00  --inst_learning_loop_flag               true
% 3.17/1.00  --inst_learning_start                   3000
% 3.17/1.00  --inst_learning_factor                  2
% 3.17/1.00  --inst_start_prop_sim_after_learn       3
% 3.17/1.00  --inst_sel_renew                        solver
% 3.17/1.00  --inst_lit_activity_flag                true
% 3.17/1.00  --inst_restr_to_given                   false
% 3.17/1.00  --inst_activity_threshold               500
% 3.17/1.00  --inst_out_proof                        true
% 3.17/1.00  
% 3.17/1.00  ------ Resolution Options
% 3.17/1.00  
% 3.17/1.00  --resolution_flag                       false
% 3.17/1.00  --res_lit_sel                           adaptive
% 3.17/1.00  --res_lit_sel_side                      none
% 3.17/1.00  --res_ordering                          kbo
% 3.17/1.00  --res_to_prop_solver                    active
% 3.17/1.00  --res_prop_simpl_new                    false
% 3.17/1.00  --res_prop_simpl_given                  true
% 3.17/1.00  --res_passive_queue_type                priority_queues
% 3.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.00  --res_passive_queues_freq               [15;5]
% 3.17/1.00  --res_forward_subs                      full
% 3.17/1.00  --res_backward_subs                     full
% 3.17/1.00  --res_forward_subs_resolution           true
% 3.17/1.00  --res_backward_subs_resolution          true
% 3.17/1.00  --res_orphan_elimination                true
% 3.17/1.00  --res_time_limit                        2.
% 3.17/1.00  --res_out_proof                         true
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Options
% 3.17/1.00  
% 3.17/1.00  --superposition_flag                    true
% 3.17/1.00  --sup_passive_queue_type                priority_queues
% 3.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.00  --demod_completeness_check              fast
% 3.17/1.00  --demod_use_ground                      true
% 3.17/1.00  --sup_to_prop_solver                    passive
% 3.17/1.00  --sup_prop_simpl_new                    true
% 3.17/1.00  --sup_prop_simpl_given                  true
% 3.17/1.00  --sup_fun_splitting                     false
% 3.17/1.00  --sup_smt_interval                      50000
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Simplification Setup
% 3.17/1.00  
% 3.17/1.00  --sup_indices_passive                   []
% 3.17/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_full_bw                           [BwDemod]
% 3.17/1.00  --sup_immed_triv                        [TrivRules]
% 3.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_immed_bw_main                     []
% 3.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  
% 3.17/1.00  ------ Combination Options
% 3.17/1.00  
% 3.17/1.00  --comb_res_mult                         3
% 3.17/1.00  --comb_sup_mult                         2
% 3.17/1.00  --comb_inst_mult                        10
% 3.17/1.00  
% 3.17/1.00  ------ Debug Options
% 3.17/1.00  
% 3.17/1.00  --dbg_backtrace                         false
% 3.17/1.00  --dbg_dump_prop_clauses                 false
% 3.17/1.00  --dbg_dump_prop_clauses_file            -
% 3.17/1.00  --dbg_out_stat                          false
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  ------ Proving...
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  % SZS status Theorem for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  fof(f11,axiom,(
% 3.17/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f29,plain,(
% 3.17/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.17/1.00    inference(ennf_transformation,[],[f11])).
% 3.17/1.00  
% 3.17/1.00  fof(f30,plain,(
% 3.17/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(flattening,[],[f29])).
% 3.17/1.00  
% 3.17/1.00  fof(f43,plain,(
% 3.17/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(nnf_transformation,[],[f30])).
% 3.17/1.00  
% 3.17/1.00  fof(f62,plain,(
% 3.17/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f43])).
% 3.17/1.00  
% 3.17/1.00  fof(f18,conjecture,(
% 3.17/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f19,negated_conjecture,(
% 3.17/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.17/1.00    inference(negated_conjecture,[],[f18])).
% 3.17/1.00  
% 3.17/1.00  fof(f39,plain,(
% 3.17/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.17/1.00    inference(ennf_transformation,[],[f19])).
% 3.17/1.00  
% 3.17/1.00  fof(f40,plain,(
% 3.17/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.17/1.00    inference(flattening,[],[f39])).
% 3.17/1.00  
% 3.17/1.00  fof(f46,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f45,plain,(
% 3.17/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f47,plain,(
% 3.17/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f46,f45])).
% 3.17/1.00  
% 3.17/1.00  fof(f79,plain,(
% 3.17/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f14,axiom,(
% 3.17/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f20,plain,(
% 3.17/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.17/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.17/1.00  
% 3.17/1.00  fof(f68,plain,(
% 3.17/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f20])).
% 3.17/1.00  
% 3.17/1.00  fof(f73,plain,(
% 3.17/1.00    v1_funct_1(sK2)),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f75,plain,(
% 3.17/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f76,plain,(
% 3.17/1.00    v1_funct_1(sK3)),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f78,plain,(
% 3.17/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f13,axiom,(
% 3.17/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f33,plain,(
% 3.17/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.17/1.00    inference(ennf_transformation,[],[f13])).
% 3.17/1.00  
% 3.17/1.00  fof(f34,plain,(
% 3.17/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.17/1.00    inference(flattening,[],[f33])).
% 3.17/1.00  
% 3.17/1.00  fof(f67,plain,(
% 3.17/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f34])).
% 3.17/1.00  
% 3.17/1.00  fof(f17,axiom,(
% 3.17/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f37,plain,(
% 3.17/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.17/1.00    inference(ennf_transformation,[],[f17])).
% 3.17/1.00  
% 3.17/1.00  fof(f38,plain,(
% 3.17/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.17/1.00    inference(flattening,[],[f37])).
% 3.17/1.00  
% 3.17/1.00  fof(f71,plain,(
% 3.17/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f38])).
% 3.17/1.00  
% 3.17/1.00  fof(f74,plain,(
% 3.17/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f77,plain,(
% 3.17/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f4,axiom,(
% 3.17/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f23,plain,(
% 3.17/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f4])).
% 3.17/1.00  
% 3.17/1.00  fof(f53,plain,(
% 3.17/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f23])).
% 3.17/1.00  
% 3.17/1.00  fof(f5,axiom,(
% 3.17/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f54,plain,(
% 3.17/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f5])).
% 3.17/1.00  
% 3.17/1.00  fof(f10,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f28,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(ennf_transformation,[],[f10])).
% 3.17/1.00  
% 3.17/1.00  fof(f61,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f28])).
% 3.17/1.00  
% 3.17/1.00  fof(f16,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f35,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.17/1.00    inference(ennf_transformation,[],[f16])).
% 3.17/1.00  
% 3.17/1.00  fof(f36,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.17/1.00    inference(flattening,[],[f35])).
% 3.17/1.00  
% 3.17/1.00  fof(f70,plain,(
% 3.17/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f36])).
% 3.17/1.00  
% 3.17/1.00  fof(f63,plain,(
% 3.17/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f43])).
% 3.17/1.00  
% 3.17/1.00  fof(f84,plain,(
% 3.17/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(equality_resolution,[],[f63])).
% 3.17/1.00  
% 3.17/1.00  fof(f9,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f21,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.17/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.17/1.00  
% 3.17/1.00  fof(f27,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(ennf_transformation,[],[f21])).
% 3.17/1.00  
% 3.17/1.00  fof(f60,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f27])).
% 3.17/1.00  
% 3.17/1.00  fof(f12,axiom,(
% 3.17/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f31,plain,(
% 3.17/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.17/1.00    inference(ennf_transformation,[],[f12])).
% 3.17/1.00  
% 3.17/1.00  fof(f32,plain,(
% 3.17/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.17/1.00    inference(flattening,[],[f31])).
% 3.17/1.00  
% 3.17/1.00  fof(f44,plain,(
% 3.17/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.17/1.00    inference(nnf_transformation,[],[f32])).
% 3.17/1.00  
% 3.17/1.00  fof(f65,plain,(
% 3.17/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f44])).
% 3.17/1.00  
% 3.17/1.00  fof(f85,plain,(
% 3.17/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.17/1.00    inference(equality_resolution,[],[f65])).
% 3.17/1.00  
% 3.17/1.00  fof(f80,plain,(
% 3.17/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f8,axiom,(
% 3.17/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f59,plain,(
% 3.17/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f8])).
% 3.17/1.00  
% 3.17/1.00  fof(f15,axiom,(
% 3.17/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f69,plain,(
% 3.17/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f15])).
% 3.17/1.00  
% 3.17/1.00  fof(f81,plain,(
% 3.17/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.17/1.00    inference(definition_unfolding,[],[f59,f69])).
% 3.17/1.00  
% 3.17/1.00  fof(f3,axiom,(
% 3.17/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f22,plain,(
% 3.17/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f3])).
% 3.17/1.00  
% 3.17/1.00  fof(f52,plain,(
% 3.17/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f22])).
% 3.17/1.00  
% 3.17/1.00  fof(f7,axiom,(
% 3.17/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f25,plain,(
% 3.17/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 3.17/1.00    inference(ennf_transformation,[],[f7])).
% 3.17/1.00  
% 3.17/1.00  fof(f26,plain,(
% 3.17/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.17/1.00    inference(flattening,[],[f25])).
% 3.17/1.00  
% 3.17/1.00  fof(f58,plain,(
% 3.17/1.00    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f26])).
% 3.17/1.00  
% 3.17/1.00  fof(f6,axiom,(
% 3.17/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f24,plain,(
% 3.17/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f6])).
% 3.17/1.00  
% 3.17/1.00  fof(f55,plain,(
% 3.17/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f24])).
% 3.17/1.00  
% 3.17/1.00  fof(f2,axiom,(
% 3.17/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f41,plain,(
% 3.17/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.17/1.00    inference(nnf_transformation,[],[f2])).
% 3.17/1.00  
% 3.17/1.00  fof(f42,plain,(
% 3.17/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.17/1.00    inference(flattening,[],[f41])).
% 3.17/1.00  
% 3.17/1.00  fof(f50,plain,(
% 3.17/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.17/1.00    inference(cnf_transformation,[],[f42])).
% 3.17/1.00  
% 3.17/1.00  fof(f83,plain,(
% 3.17/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.17/1.00    inference(equality_resolution,[],[f50])).
% 3.17/1.00  
% 3.17/1.00  fof(f1,axiom,(
% 3.17/1.00    v1_xboole_0(k1_xboole_0)),
% 3.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f48,plain,(
% 3.17/1.00    v1_xboole_0(k1_xboole_0)),
% 3.17/1.00    inference(cnf_transformation,[],[f1])).
% 3.17/1.00  
% 3.17/1.00  cnf(c_15,plain,
% 3.17/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.17/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | X3 = X2 ),
% 3.17/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_25,negated_conjecture,
% 3.17/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_437,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | X3 = X0
% 3.17/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.17/1.00      | k6_partfun1(sK0) != X3
% 3.17/1.00      | sK0 != X2
% 3.17/1.00      | sK0 != X1 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_438,plain,
% 3.17/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.17/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.17/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_437]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_20,plain,
% 3.17/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.17/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_446,plain,
% 3.17/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.17/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.17/1.00      inference(forward_subsumption_resolution,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_438,c_20]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1120,plain,
% 3.17/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.17/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_31,negated_conjecture,
% 3.17/1.00      ( v1_funct_1(sK2) ),
% 3.17/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_29,negated_conjecture,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.17/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_28,negated_conjecture,
% 3.17/1.00      ( v1_funct_1(sK3) ),
% 3.17/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_26,negated_conjecture,
% 3.17/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.17/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_18,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.17/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X3) ),
% 3.17/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1446,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.17/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(sK3) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1610,plain,
% 3.17/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.17/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.17/1.00      | ~ v1_funct_1(sK2)
% 3.17/1.00      | ~ v1_funct_1(sK3) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_1446]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1714,plain,
% 3.17/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_1120,c_31,c_29,c_28,c_26,c_446,c_1610]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_23,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | v2_funct_1(X3)
% 3.17/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X3)
% 3.17/1.00      | k1_xboole_0 = X2 ),
% 3.17/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1131,plain,
% 3.17/1.00      ( k1_xboole_0 = X0
% 3.17/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.17/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.17/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.17/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.17/1.00      | v2_funct_1(X3) = iProver_top
% 3.17/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
% 3.17/1.00      | v1_funct_1(X1) != iProver_top
% 3.17/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4675,plain,
% 3.17/1.00      ( sK0 = k1_xboole_0
% 3.17/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.17/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.17/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.17/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.17/1.00      | v2_funct_1(sK2) = iProver_top
% 3.17/1.00      | v1_funct_1(sK2) != iProver_top
% 3.17/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1714,c_1131]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_32,plain,
% 3.17/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_30,negated_conjecture,
% 3.17/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_33,plain,
% 3.17/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_34,plain,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_35,plain,
% 3.17/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_27,negated_conjecture,
% 3.17/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_36,plain,
% 3.17/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_37,plain,
% 3.17/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_5,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.17/1.00      | ~ v1_relat_1(X1)
% 3.17/1.00      | v1_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1372,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | v1_relat_1(X0)
% 3.17/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1583,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.17/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.17/1.00      | v1_relat_1(sK3) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_1372]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1584,plain,
% 3.17/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.17/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.17/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_6,plain,
% 3.17/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1853,plain,
% 3.17/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1854,plain,
% 3.17/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1853]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1130,plain,
% 3.17/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_13,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1136,plain,
% 3.17/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.17/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2279,plain,
% 3.17/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1130,c_1136]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_21,plain,
% 3.17/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.17/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.17/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.17/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | ~ v1_funct_1(X2)
% 3.17/1.00      | ~ v1_funct_1(X3)
% 3.17/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_450,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X3)
% 3.17/1.00      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) = X2
% 3.17/1.00      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.17/1.00      | sK0 != X2 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_451,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.17/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.17/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X2)
% 3.17/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.17/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 3.17/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_450]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_528,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.17/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.17/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X2)
% 3.17/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.17/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.17/1.00      inference(equality_resolution_simp,[status(thm)],[c_451]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1119,plain,
% 3.17/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.17/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 3.17/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.17/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.17/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.17/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.17/1.00      | v1_funct_1(X2) != iProver_top
% 3.17/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1787,plain,
% 3.17/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
% 3.17/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 3.17/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.17/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.17/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.17/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.17/1.00      | v1_funct_1(X1) != iProver_top
% 3.17/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_1119,c_1714]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1799,plain,
% 3.17/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.17/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.17/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.17/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.17/1.00      | v1_funct_1(sK2) != iProver_top
% 3.17/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1714,c_1787]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_14,plain,
% 3.17/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.17/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.17/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_402,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.17/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X3)
% 3.17/1.00      | X1 != X6
% 3.17/1.00      | X1 != X5
% 3.17/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != X4
% 3.17/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.17/1.00      | k6_partfun1(X1) != X4 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_403,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.17/1.00      | ~ m1_subset_1(k1_partfun1(X1,X2,X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X3)
% 3.17/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.17/1.00      | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_402]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_425,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X3)
% 3.17/1.00      | k2_relset_1(X2,X1,X3) = X1
% 3.17/1.00      | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
% 3.17/1.00      inference(forward_subsumption_resolution,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_403,c_18]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1461,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,sK1,sK0)
% 3.17/1.00      | ~ v1_funct_2(sK2,sK0,sK1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(sK1,sK0,X0) = sK0
% 3.17/1.00      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_425]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1508,plain,
% 3.17/1.00      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.17/1.00      | ~ v1_funct_2(sK3,sK1,sK0)
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.17/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.17/1.00      | ~ v1_funct_1(sK2)
% 3.17/1.00      | ~ v1_funct_1(sK3)
% 3.17/1.00      | k2_relset_1(sK1,sK0,sK3) = sK0
% 3.17/1.00      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_1461]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1860,plain,
% 3.17/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_1799,c_31,c_30,c_29,c_28,c_27,c_26,c_446,c_1508,
% 3.17/1.00                 c_1610]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2294,plain,
% 3.17/1.00      ( k2_relat_1(sK3) = sK0 ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_2279,c_1860]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_12,plain,
% 3.17/1.00      ( v5_relat_1(X0,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.17/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_16,plain,
% 3.17/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.17/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.17/1.00      | ~ v1_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_24,negated_conjecture,
% 3.17/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.17/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_356,plain,
% 3.17/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.17/1.00      | ~ v2_funct_1(sK2)
% 3.17/1.00      | ~ v1_relat_1(X0)
% 3.17/1.00      | k2_relat_1(X0) != sK0
% 3.17/1.00      | sK3 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_357,plain,
% 3.17/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.17/1.00      | ~ v2_funct_1(sK2)
% 3.17/1.00      | ~ v1_relat_1(sK3)
% 3.17/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_356]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_377,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v2_funct_1(sK2)
% 3.17/1.00      | ~ v1_relat_1(sK3)
% 3.17/1.00      | k2_relat_1(sK3) != X2
% 3.17/1.00      | k2_relat_1(sK3) != sK0
% 3.17/1.00      | sK3 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_357]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_378,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.17/1.00      | ~ v2_funct_1(sK2)
% 3.17/1.00      | ~ v1_relat_1(sK3)
% 3.17/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_377]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_665,plain,
% 3.17/1.00      ( ~ v2_funct_1(sK2)
% 3.17/1.00      | ~ v1_relat_1(sK3)
% 3.17/1.00      | sP0_iProver_split
% 3.17/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.17/1.00      inference(splitting,
% 3.17/1.00                [splitting(split),new_symbols(definition,[])],
% 3.17/1.00                [c_378]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1122,plain,
% 3.17/1.00      ( k2_relat_1(sK3) != sK0
% 3.17/1.00      | v2_funct_1(sK2) != iProver_top
% 3.17/1.00      | v1_relat_1(sK3) != iProver_top
% 3.17/1.00      | sP0_iProver_split = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2665,plain,
% 3.17/1.00      ( sK0 != sK0
% 3.17/1.00      | v2_funct_1(sK2) != iProver_top
% 3.17/1.00      | v1_relat_1(sK3) != iProver_top
% 3.17/1.00      | sP0_iProver_split = iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_2294,c_1122]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2671,plain,
% 3.17/1.00      ( v2_funct_1(sK2) != iProver_top
% 3.17/1.00      | v1_relat_1(sK3) != iProver_top
% 3.17/1.00      | sP0_iProver_split = iProver_top ),
% 3.17/1.00      inference(equality_resolution_simp,[status(thm)],[c_2665]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_664,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.17/1.00      | ~ sP0_iProver_split ),
% 3.17/1.00      inference(splitting,
% 3.17/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.17/1.00                [c_378]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1123,plain,
% 3.17/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.17/1.00      | sP0_iProver_split != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2666,plain,
% 3.17/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.17/1.00      | sP0_iProver_split != iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_2294,c_1123]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2685,plain,
% 3.17/1.00      ( sP0_iProver_split != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1130,c_2666]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4907,plain,
% 3.17/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_4675,c_32,c_33,c_34,c_35,c_36,c_37,c_1584,c_1854,
% 3.17/1.00                 c_2671,c_2685]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4908,plain,
% 3.17/1.00      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.17/1.00      inference(renaming,[status(thm)],[c_4907]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_11,plain,
% 3.17/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1137,plain,
% 3.17/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4913,plain,
% 3.17/1.00      ( sK0 = k1_xboole_0 ),
% 3.17/1.00      inference(forward_subsumption_resolution,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_4908,c_1137]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1127,plain,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.17/1.00      | ~ v1_xboole_0(X1)
% 3.17/1.00      | v1_xboole_0(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1141,plain,
% 3.17/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.17/1.00      | v1_xboole_0(X1) != iProver_top
% 3.17/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3961,plain,
% 3.17/1.00      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.17/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1127,c_1141]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1586,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.17/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.17/1.00      | v1_relat_1(sK2) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_1372]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1587,plain,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.17/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.17/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1856,plain,
% 3.17/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1857,plain,
% 3.17/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_1856]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_8,plain,
% 3.17/1.00      ( v2_funct_1(X0)
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_relat_1(X0)
% 3.17/1.00      | ~ v1_xboole_0(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7,plain,
% 3.17/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_175,plain,
% 3.17/1.00      ( v2_funct_1(X0) | ~ v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.17/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8,c_7]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2538,plain,
% 3.17/1.00      ( v2_funct_1(sK2) | ~ v1_relat_1(sK2) | ~ v1_xboole_0(sK2) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_175]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2539,plain,
% 3.17/1.00      ( v2_funct_1(sK2) = iProver_top
% 3.17/1.00      | v1_relat_1(sK2) != iProver_top
% 3.17/1.00      | v1_xboole_0(sK2) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_2538]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4176,plain,
% 3.17/1.00      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_3961,c_34,c_37,c_1584,c_1587,c_1854,c_1857,c_2539,
% 3.17/1.00                 c_2671,c_2685]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4915,plain,
% 3.17/1.00      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_4913,c_4176]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2,plain,
% 3.17/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4967,plain,
% 3.17/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_4915,c_2]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_0,plain,
% 3.17/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_94,plain,
% 3.17/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(contradiction,plain,
% 3.17/1.00      ( $false ),
% 3.17/1.00      inference(minisat,[status(thm)],[c_4967,c_94]) ).
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  ------                               Statistics
% 3.17/1.00  
% 3.17/1.00  ------ General
% 3.17/1.00  
% 3.17/1.00  abstr_ref_over_cycles:                  0
% 3.17/1.00  abstr_ref_under_cycles:                 0
% 3.17/1.00  gc_basic_clause_elim:                   0
% 3.17/1.00  forced_gc_time:                         0
% 3.17/1.00  parsing_time:                           0.018
% 3.17/1.00  unif_index_cands_time:                  0.
% 3.17/1.00  unif_index_add_time:                    0.
% 3.17/1.00  orderings_time:                         0.
% 3.17/1.00  out_proof_time:                         0.012
% 3.17/1.00  total_time:                             0.196
% 3.17/1.00  num_of_symbols:                         52
% 3.17/1.00  num_of_terms:                           5067
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing
% 3.17/1.00  
% 3.17/1.00  num_of_splits:                          1
% 3.17/1.00  num_of_split_atoms:                     1
% 3.17/1.00  num_of_reused_defs:                     0
% 3.17/1.00  num_eq_ax_congr_red:                    9
% 3.17/1.00  num_of_sem_filtered_clauses:            1
% 3.17/1.00  num_of_subtypes:                        0
% 3.17/1.00  monotx_restored_types:                  0
% 3.17/1.00  sat_num_of_epr_types:                   0
% 3.17/1.00  sat_num_of_non_cyclic_types:            0
% 3.17/1.00  sat_guarded_non_collapsed_types:        0
% 3.17/1.00  num_pure_diseq_elim:                    0
% 3.17/1.00  simp_replaced_by:                       0
% 3.17/1.00  res_preprocessed:                       139
% 3.17/1.00  prep_upred:                             0
% 3.17/1.00  prep_unflattend:                        19
% 3.17/1.00  smt_new_axioms:                         0
% 3.17/1.00  pred_elim_cands:                        6
% 3.17/1.00  pred_elim:                              3
% 3.17/1.00  pred_elim_cl:                           4
% 3.17/1.00  pred_elim_cycles:                       6
% 3.17/1.00  merged_defs:                            0
% 3.17/1.00  merged_defs_ncl:                        0
% 3.17/1.00  bin_hyper_res:                          0
% 3.17/1.00  prep_cycles:                            4
% 3.17/1.00  pred_elim_time:                         0.006
% 3.17/1.00  splitting_time:                         0.
% 3.17/1.00  sem_filter_time:                        0.
% 3.17/1.00  monotx_time:                            0.
% 3.17/1.00  subtype_inf_time:                       0.
% 3.17/1.00  
% 3.17/1.00  ------ Problem properties
% 3.17/1.00  
% 3.17/1.00  clauses:                                27
% 3.17/1.00  conjectures:                            6
% 3.17/1.00  epr:                                    7
% 3.17/1.00  horn:                                   25
% 3.17/1.00  ground:                                 9
% 3.17/1.00  unary:                                  12
% 3.17/1.00  binary:                                 4
% 3.17/1.00  lits:                                   79
% 3.17/1.00  lits_eq:                                13
% 3.17/1.00  fd_pure:                                0
% 3.17/1.00  fd_pseudo:                              0
% 3.17/1.00  fd_cond:                                2
% 3.17/1.00  fd_pseudo_cond:                         0
% 3.17/1.00  ac_symbols:                             0
% 3.17/1.00  
% 3.17/1.00  ------ Propositional Solver
% 3.17/1.00  
% 3.17/1.00  prop_solver_calls:                      29
% 3.17/1.00  prop_fast_solver_calls:                 1007
% 3.17/1.00  smt_solver_calls:                       0
% 3.17/1.00  smt_fast_solver_calls:                  0
% 3.17/1.00  prop_num_of_clauses:                    1994
% 3.17/1.00  prop_preprocess_simplified:             6646
% 3.17/1.00  prop_fo_subsumed:                       25
% 3.17/1.00  prop_solver_time:                       0.
% 3.17/1.00  smt_solver_time:                        0.
% 3.17/1.00  smt_fast_solver_time:                   0.
% 3.17/1.00  prop_fast_solver_time:                  0.
% 3.17/1.00  prop_unsat_core_time:                   0.
% 3.17/1.00  
% 3.17/1.00  ------ QBF
% 3.17/1.00  
% 3.17/1.00  qbf_q_res:                              0
% 3.17/1.00  qbf_num_tautologies:                    0
% 3.17/1.00  qbf_prep_cycles:                        0
% 3.17/1.00  
% 3.17/1.00  ------ BMC1
% 3.17/1.00  
% 3.17/1.00  bmc1_current_bound:                     -1
% 3.17/1.00  bmc1_last_solved_bound:                 -1
% 3.17/1.00  bmc1_unsat_core_size:                   -1
% 3.17/1.00  bmc1_unsat_core_parents_size:           -1
% 3.17/1.00  bmc1_merge_next_fun:                    0
% 3.17/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation
% 3.17/1.00  
% 3.17/1.00  inst_num_of_clauses:                    728
% 3.17/1.00  inst_num_in_passive:                    488
% 3.17/1.00  inst_num_in_active:                     233
% 3.17/1.00  inst_num_in_unprocessed:                7
% 3.17/1.00  inst_num_of_loops:                      260
% 3.17/1.00  inst_num_of_learning_restarts:          0
% 3.17/1.00  inst_num_moves_active_passive:          25
% 3.17/1.00  inst_lit_activity:                      0
% 3.17/1.00  inst_lit_activity_moves:                1
% 3.17/1.00  inst_num_tautologies:                   0
% 3.17/1.00  inst_num_prop_implied:                  0
% 3.17/1.00  inst_num_existing_simplified:           0
% 3.17/1.00  inst_num_eq_res_simplified:             0
% 3.17/1.00  inst_num_child_elim:                    0
% 3.17/1.00  inst_num_of_dismatching_blockings:      16
% 3.17/1.00  inst_num_of_non_proper_insts:           299
% 3.17/1.00  inst_num_of_duplicates:                 0
% 3.17/1.00  inst_inst_num_from_inst_to_res:         0
% 3.17/1.00  inst_dismatching_checking_time:         0.
% 3.17/1.00  
% 3.17/1.00  ------ Resolution
% 3.17/1.00  
% 3.17/1.00  res_num_of_clauses:                     0
% 3.17/1.00  res_num_in_passive:                     0
% 3.17/1.00  res_num_in_active:                      0
% 3.17/1.00  res_num_of_loops:                       143
% 3.17/1.00  res_forward_subset_subsumed:            5
% 3.17/1.00  res_backward_subset_subsumed:           0
% 3.17/1.00  res_forward_subsumed:                   0
% 3.17/1.00  res_backward_subsumed:                  0
% 3.17/1.00  res_forward_subsumption_resolution:     2
% 3.17/1.00  res_backward_subsumption_resolution:    0
% 3.17/1.00  res_clause_to_clause_subsumption:       115
% 3.17/1.00  res_orphan_elimination:                 0
% 3.17/1.00  res_tautology_del:                      10
% 3.17/1.00  res_num_eq_res_simplified:              1
% 3.17/1.00  res_num_sel_changes:                    0
% 3.17/1.00  res_moves_from_active_to_pass:          0
% 3.17/1.00  
% 3.17/1.00  ------ Superposition
% 3.17/1.00  
% 3.17/1.00  sup_time_total:                         0.
% 3.17/1.00  sup_time_generating:                    0.
% 3.17/1.00  sup_time_sim_full:                      0.
% 3.17/1.00  sup_time_sim_immed:                     0.
% 3.17/1.00  
% 3.17/1.00  sup_num_of_clauses:                     66
% 3.17/1.00  sup_num_in_active:                      36
% 3.17/1.00  sup_num_in_passive:                     30
% 3.17/1.00  sup_num_of_loops:                       51
% 3.17/1.00  sup_fw_superposition:                   33
% 3.17/1.00  sup_bw_superposition:                   14
% 3.17/1.00  sup_immediate_simplified:               10
% 3.17/1.00  sup_given_eliminated:                   1
% 3.17/1.00  comparisons_done:                       0
% 3.17/1.00  comparisons_avoided:                    0
% 3.17/1.00  
% 3.17/1.00  ------ Simplifications
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  sim_fw_subset_subsumed:                 0
% 3.17/1.00  sim_bw_subset_subsumed:                 0
% 3.17/1.00  sim_fw_subsumed:                        1
% 3.17/1.00  sim_bw_subsumed:                        2
% 3.17/1.00  sim_fw_subsumption_res:                 1
% 3.17/1.00  sim_bw_subsumption_res:                 0
% 3.17/1.00  sim_tautology_del:                      0
% 3.17/1.00  sim_eq_tautology_del:                   1
% 3.17/1.00  sim_eq_res_simp:                        1
% 3.17/1.00  sim_fw_demodulated:                     7
% 3.17/1.00  sim_bw_demodulated:                     14
% 3.17/1.00  sim_light_normalised:                   3
% 3.17/1.00  sim_joinable_taut:                      0
% 3.17/1.00  sim_joinable_simp:                      0
% 3.17/1.00  sim_ac_normalised:                      0
% 3.17/1.00  sim_smt_subsumption:                    0
% 3.17/1.00  
%------------------------------------------------------------------------------

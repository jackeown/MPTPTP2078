%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:46 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  191 (2095 expanded)
%              Number of clauses        :  101 ( 594 expanded)
%              Number of leaves         :   25 ( 531 expanded)
%              Depth                    :   21
%              Number of atoms          :  614 (13717 expanded)
%              Number of equality atoms :  193 ( 996 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f54,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f53,f52])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f21,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f94,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f84])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1222,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1225,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3683,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1225])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3719,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3683,c_42])).

cnf(c_3720,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3719])).

cnf(c_3730,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_3720])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1839,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_2303,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_3599,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_3767,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3730,c_38,c_36,c_35,c_33,c_3599])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1223,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3773,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3767,c_1223])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_18,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_31,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_422,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_423,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_476,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_423])).

cnf(c_477,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_487,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_477,c_2])).

cnf(c_488,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2815,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1234])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1233,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2981,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2815,c_1233])).

cnf(c_2816,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1234])).

cnf(c_2986,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2816,c_1233])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_9])).

cnf(c_1214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_2648,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1214])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1239,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2929,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2648,c_1239])).

cnf(c_3919,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2929,c_2981])).

cnf(c_3920,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3919])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_404,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_69,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_406,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_69])).

cnf(c_1215,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_3770,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3767,c_1215])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4095,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3767,c_1227])).

cnf(c_4336,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3770,c_39,c_41,c_42,c_44,c_4095])).

cnf(c_11,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1232,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4340,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4336,c_1232])).

cnf(c_12,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4341,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4340,c_12])).

cnf(c_4339,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_4336,c_3767])).

cnf(c_4541,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_1223])).

cnf(c_8284,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3773,c_39,c_40,c_41,c_42,c_43,c_44,c_85,c_488,c_2929,c_2981,c_2986,c_4341,c_4541])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2833,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1236])).

cnf(c_8321,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8284,c_2833])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_123,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_692,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1593,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_1594,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1593])).

cnf(c_1596,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1237,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3130,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_2833])).

cnf(c_9312,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8321,c_39,c_40,c_41,c_42,c_43,c_44,c_85,c_123,c_488,c_1596,c_2929,c_2981,c_2986,c_3130,c_4341,c_4541])).

cnf(c_15,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_14,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_220,plain,
    ( v2_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_14,c_6])).

cnf(c_1216,plain,
    ( v2_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_9319,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9312,c_1216])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9319,c_4341,c_3920,c_2986,c_2981,c_488])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.09/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/1.00  
% 3.09/1.00  ------  iProver source info
% 3.09/1.00  
% 3.09/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.09/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/1.00  git: non_committed_changes: false
% 3.09/1.00  git: last_make_outside_of_git: false
% 3.09/1.00  
% 3.09/1.00  ------ 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options
% 3.09/1.00  
% 3.09/1.00  --out_options                           all
% 3.09/1.00  --tptp_safe_out                         true
% 3.09/1.00  --problem_path                          ""
% 3.09/1.00  --include_path                          ""
% 3.09/1.00  --clausifier                            res/vclausify_rel
% 3.09/1.00  --clausifier_options                    --mode clausify
% 3.09/1.00  --stdin                                 false
% 3.09/1.00  --stats_out                             all
% 3.09/1.00  
% 3.09/1.00  ------ General Options
% 3.09/1.00  
% 3.09/1.00  --fof                                   false
% 3.09/1.00  --time_out_real                         305.
% 3.09/1.00  --time_out_virtual                      -1.
% 3.09/1.00  --symbol_type_check                     false
% 3.09/1.00  --clausify_out                          false
% 3.09/1.00  --sig_cnt_out                           false
% 3.09/1.00  --trig_cnt_out                          false
% 3.09/1.00  --trig_cnt_out_tolerance                1.
% 3.09/1.00  --trig_cnt_out_sk_spl                   false
% 3.09/1.00  --abstr_cl_out                          false
% 3.09/1.00  
% 3.09/1.00  ------ Global Options
% 3.09/1.00  
% 3.09/1.00  --schedule                              default
% 3.09/1.00  --add_important_lit                     false
% 3.09/1.00  --prop_solver_per_cl                    1000
% 3.09/1.00  --min_unsat_core                        false
% 3.09/1.00  --soft_assumptions                      false
% 3.09/1.00  --soft_lemma_size                       3
% 3.09/1.00  --prop_impl_unit_size                   0
% 3.09/1.00  --prop_impl_unit                        []
% 3.09/1.00  --share_sel_clauses                     true
% 3.09/1.00  --reset_solvers                         false
% 3.09/1.00  --bc_imp_inh                            [conj_cone]
% 3.09/1.00  --conj_cone_tolerance                   3.
% 3.09/1.00  --extra_neg_conj                        none
% 3.09/1.00  --large_theory_mode                     true
% 3.09/1.00  --prolific_symb_bound                   200
% 3.09/1.00  --lt_threshold                          2000
% 3.09/1.00  --clause_weak_htbl                      true
% 3.09/1.00  --gc_record_bc_elim                     false
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing Options
% 3.09/1.00  
% 3.09/1.00  --preprocessing_flag                    true
% 3.09/1.00  --time_out_prep_mult                    0.1
% 3.09/1.00  --splitting_mode                        input
% 3.09/1.00  --splitting_grd                         true
% 3.09/1.00  --splitting_cvd                         false
% 3.09/1.00  --splitting_cvd_svl                     false
% 3.09/1.00  --splitting_nvd                         32
% 3.09/1.00  --sub_typing                            true
% 3.09/1.00  --prep_gs_sim                           true
% 3.09/1.00  --prep_unflatten                        true
% 3.09/1.00  --prep_res_sim                          true
% 3.09/1.00  --prep_upred                            true
% 3.09/1.00  --prep_sem_filter                       exhaustive
% 3.09/1.00  --prep_sem_filter_out                   false
% 3.09/1.00  --pred_elim                             true
% 3.09/1.00  --res_sim_input                         true
% 3.09/1.00  --eq_ax_congr_red                       true
% 3.09/1.00  --pure_diseq_elim                       true
% 3.09/1.00  --brand_transform                       false
% 3.09/1.00  --non_eq_to_eq                          false
% 3.09/1.00  --prep_def_merge                        true
% 3.09/1.00  --prep_def_merge_prop_impl              false
% 3.09/1.00  --prep_def_merge_mbd                    true
% 3.09/1.00  --prep_def_merge_tr_red                 false
% 3.09/1.00  --prep_def_merge_tr_cl                  false
% 3.09/1.00  --smt_preprocessing                     true
% 3.09/1.00  --smt_ac_axioms                         fast
% 3.09/1.00  --preprocessed_out                      false
% 3.09/1.00  --preprocessed_stats                    false
% 3.09/1.00  
% 3.09/1.00  ------ Abstraction refinement Options
% 3.09/1.00  
% 3.09/1.00  --abstr_ref                             []
% 3.09/1.00  --abstr_ref_prep                        false
% 3.09/1.00  --abstr_ref_until_sat                   false
% 3.09/1.00  --abstr_ref_sig_restrict                funpre
% 3.09/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.00  --abstr_ref_under                       []
% 3.09/1.00  
% 3.09/1.00  ------ SAT Options
% 3.09/1.00  
% 3.09/1.00  --sat_mode                              false
% 3.09/1.00  --sat_fm_restart_options                ""
% 3.09/1.00  --sat_gr_def                            false
% 3.09/1.00  --sat_epr_types                         true
% 3.09/1.00  --sat_non_cyclic_types                  false
% 3.09/1.00  --sat_finite_models                     false
% 3.09/1.00  --sat_fm_lemmas                         false
% 3.09/1.00  --sat_fm_prep                           false
% 3.09/1.00  --sat_fm_uc_incr                        true
% 3.09/1.00  --sat_out_model                         small
% 3.09/1.00  --sat_out_clauses                       false
% 3.09/1.00  
% 3.09/1.00  ------ QBF Options
% 3.09/1.00  
% 3.09/1.00  --qbf_mode                              false
% 3.09/1.00  --qbf_elim_univ                         false
% 3.09/1.00  --qbf_dom_inst                          none
% 3.09/1.00  --qbf_dom_pre_inst                      false
% 3.09/1.00  --qbf_sk_in                             false
% 3.09/1.00  --qbf_pred_elim                         true
% 3.09/1.00  --qbf_split                             512
% 3.09/1.00  
% 3.09/1.00  ------ BMC1 Options
% 3.09/1.00  
% 3.09/1.00  --bmc1_incremental                      false
% 3.09/1.00  --bmc1_axioms                           reachable_all
% 3.09/1.00  --bmc1_min_bound                        0
% 3.09/1.00  --bmc1_max_bound                        -1
% 3.09/1.00  --bmc1_max_bound_default                -1
% 3.09/1.00  --bmc1_symbol_reachability              true
% 3.09/1.00  --bmc1_property_lemmas                  false
% 3.09/1.00  --bmc1_k_induction                      false
% 3.09/1.00  --bmc1_non_equiv_states                 false
% 3.09/1.00  --bmc1_deadlock                         false
% 3.09/1.00  --bmc1_ucm                              false
% 3.09/1.00  --bmc1_add_unsat_core                   none
% 3.09/1.00  --bmc1_unsat_core_children              false
% 3.09/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.00  --bmc1_out_stat                         full
% 3.09/1.00  --bmc1_ground_init                      false
% 3.09/1.00  --bmc1_pre_inst_next_state              false
% 3.09/1.00  --bmc1_pre_inst_state                   false
% 3.09/1.00  --bmc1_pre_inst_reach_state             false
% 3.09/1.00  --bmc1_out_unsat_core                   false
% 3.09/1.00  --bmc1_aig_witness_out                  false
% 3.09/1.00  --bmc1_verbose                          false
% 3.09/1.00  --bmc1_dump_clauses_tptp                false
% 3.09/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.00  --bmc1_dump_file                        -
% 3.09/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.00  --bmc1_ucm_extend_mode                  1
% 3.09/1.00  --bmc1_ucm_init_mode                    2
% 3.09/1.00  --bmc1_ucm_cone_mode                    none
% 3.09/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.00  --bmc1_ucm_relax_model                  4
% 3.09/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.00  --bmc1_ucm_layered_model                none
% 3.09/1.00  --bmc1_ucm_max_lemma_size               10
% 3.09/1.00  
% 3.09/1.00  ------ AIG Options
% 3.09/1.00  
% 3.09/1.00  --aig_mode                              false
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation Options
% 3.09/1.00  
% 3.09/1.00  --instantiation_flag                    true
% 3.09/1.00  --inst_sos_flag                         false
% 3.09/1.00  --inst_sos_phase                        true
% 3.09/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel_side                     num_symb
% 3.09/1.00  --inst_solver_per_active                1400
% 3.09/1.00  --inst_solver_calls_frac                1.
% 3.09/1.00  --inst_passive_queue_type               priority_queues
% 3.09/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.00  --inst_passive_queues_freq              [25;2]
% 3.09/1.00  --inst_dismatching                      true
% 3.09/1.00  --inst_eager_unprocessed_to_passive     true
% 3.09/1.00  --inst_prop_sim_given                   true
% 3.09/1.00  --inst_prop_sim_new                     false
% 3.09/1.00  --inst_subs_new                         false
% 3.09/1.00  --inst_eq_res_simp                      false
% 3.09/1.00  --inst_subs_given                       false
% 3.09/1.00  --inst_orphan_elimination               true
% 3.09/1.00  --inst_learning_loop_flag               true
% 3.09/1.00  --inst_learning_start                   3000
% 3.09/1.00  --inst_learning_factor                  2
% 3.09/1.00  --inst_start_prop_sim_after_learn       3
% 3.09/1.00  --inst_sel_renew                        solver
% 3.09/1.00  --inst_lit_activity_flag                true
% 3.09/1.00  --inst_restr_to_given                   false
% 3.09/1.00  --inst_activity_threshold               500
% 3.09/1.00  --inst_out_proof                        true
% 3.09/1.00  
% 3.09/1.00  ------ Resolution Options
% 3.09/1.00  
% 3.09/1.00  --resolution_flag                       true
% 3.09/1.00  --res_lit_sel                           adaptive
% 3.09/1.00  --res_lit_sel_side                      none
% 3.09/1.00  --res_ordering                          kbo
% 3.09/1.00  --res_to_prop_solver                    active
% 3.09/1.00  --res_prop_simpl_new                    false
% 3.09/1.00  --res_prop_simpl_given                  true
% 3.09/1.00  --res_passive_queue_type                priority_queues
% 3.09/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.00  --res_passive_queues_freq               [15;5]
% 3.09/1.00  --res_forward_subs                      full
% 3.09/1.00  --res_backward_subs                     full
% 3.09/1.00  --res_forward_subs_resolution           true
% 3.09/1.00  --res_backward_subs_resolution          true
% 3.09/1.00  --res_orphan_elimination                true
% 3.09/1.00  --res_time_limit                        2.
% 3.09/1.00  --res_out_proof                         true
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Options
% 3.09/1.00  
% 3.09/1.00  --superposition_flag                    true
% 3.09/1.00  --sup_passive_queue_type                priority_queues
% 3.09/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.00  --demod_completeness_check              fast
% 3.09/1.00  --demod_use_ground                      true
% 3.09/1.00  --sup_to_prop_solver                    passive
% 3.09/1.00  --sup_prop_simpl_new                    true
% 3.09/1.00  --sup_prop_simpl_given                  true
% 3.09/1.00  --sup_fun_splitting                     false
% 3.09/1.00  --sup_smt_interval                      50000
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Simplification Setup
% 3.09/1.00  
% 3.09/1.00  --sup_indices_passive                   []
% 3.09/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_full_bw                           [BwDemod]
% 3.09/1.00  --sup_immed_triv                        [TrivRules]
% 3.09/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_immed_bw_main                     []
% 3.09/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  
% 3.09/1.00  ------ Combination Options
% 3.09/1.00  
% 3.09/1.00  --comb_res_mult                         3
% 3.09/1.00  --comb_sup_mult                         2
% 3.09/1.00  --comb_inst_mult                        10
% 3.09/1.00  
% 3.09/1.00  ------ Debug Options
% 3.09/1.00  
% 3.09/1.00  --dbg_backtrace                         false
% 3.09/1.00  --dbg_dump_prop_clauses                 false
% 3.09/1.00  --dbg_dump_prop_clauses_file            -
% 3.09/1.00  --dbg_out_stat                          false
% 3.09/1.00  ------ Parsing...
% 3.09/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/1.00  ------ Proving...
% 3.09/1.00  ------ Problem Properties 
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  clauses                                 30
% 3.09/1.00  conjectures                             6
% 3.09/1.00  EPR                                     10
% 3.09/1.00  Horn                                    29
% 3.09/1.00  unary                                   14
% 3.09/1.00  binary                                  5
% 3.09/1.00  lits                                    74
% 3.09/1.00  lits eq                                 7
% 3.09/1.00  fd_pure                                 0
% 3.09/1.00  fd_pseudo                               0
% 3.09/1.00  fd_cond                                 1
% 3.09/1.00  fd_pseudo_cond                          1
% 3.09/1.00  AC symbols                              0
% 3.09/1.00  
% 3.09/1.00  ------ Schedule dynamic 5 is on 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  ------ 
% 3.09/1.00  Current options:
% 3.09/1.00  ------ 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options
% 3.09/1.00  
% 3.09/1.00  --out_options                           all
% 3.09/1.00  --tptp_safe_out                         true
% 3.09/1.00  --problem_path                          ""
% 3.09/1.00  --include_path                          ""
% 3.09/1.00  --clausifier                            res/vclausify_rel
% 3.09/1.00  --clausifier_options                    --mode clausify
% 3.09/1.00  --stdin                                 false
% 3.09/1.00  --stats_out                             all
% 3.09/1.00  
% 3.09/1.00  ------ General Options
% 3.09/1.00  
% 3.09/1.00  --fof                                   false
% 3.09/1.00  --time_out_real                         305.
% 3.09/1.00  --time_out_virtual                      -1.
% 3.09/1.00  --symbol_type_check                     false
% 3.09/1.00  --clausify_out                          false
% 3.09/1.00  --sig_cnt_out                           false
% 3.09/1.00  --trig_cnt_out                          false
% 3.09/1.00  --trig_cnt_out_tolerance                1.
% 3.09/1.00  --trig_cnt_out_sk_spl                   false
% 3.09/1.00  --abstr_cl_out                          false
% 3.09/1.00  
% 3.09/1.00  ------ Global Options
% 3.09/1.00  
% 3.09/1.00  --schedule                              default
% 3.09/1.00  --add_important_lit                     false
% 3.09/1.00  --prop_solver_per_cl                    1000
% 3.09/1.00  --min_unsat_core                        false
% 3.09/1.00  --soft_assumptions                      false
% 3.09/1.00  --soft_lemma_size                       3
% 3.09/1.00  --prop_impl_unit_size                   0
% 3.09/1.00  --prop_impl_unit                        []
% 3.09/1.00  --share_sel_clauses                     true
% 3.09/1.00  --reset_solvers                         false
% 3.09/1.00  --bc_imp_inh                            [conj_cone]
% 3.09/1.00  --conj_cone_tolerance                   3.
% 3.09/1.00  --extra_neg_conj                        none
% 3.09/1.00  --large_theory_mode                     true
% 3.09/1.00  --prolific_symb_bound                   200
% 3.09/1.00  --lt_threshold                          2000
% 3.09/1.00  --clause_weak_htbl                      true
% 3.09/1.00  --gc_record_bc_elim                     false
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing Options
% 3.09/1.00  
% 3.09/1.00  --preprocessing_flag                    true
% 3.09/1.00  --time_out_prep_mult                    0.1
% 3.09/1.00  --splitting_mode                        input
% 3.09/1.00  --splitting_grd                         true
% 3.09/1.00  --splitting_cvd                         false
% 3.09/1.00  --splitting_cvd_svl                     false
% 3.09/1.00  --splitting_nvd                         32
% 3.09/1.00  --sub_typing                            true
% 3.09/1.00  --prep_gs_sim                           true
% 3.09/1.00  --prep_unflatten                        true
% 3.09/1.00  --prep_res_sim                          true
% 3.09/1.00  --prep_upred                            true
% 3.09/1.00  --prep_sem_filter                       exhaustive
% 3.09/1.00  --prep_sem_filter_out                   false
% 3.09/1.00  --pred_elim                             true
% 3.09/1.00  --res_sim_input                         true
% 3.09/1.00  --eq_ax_congr_red                       true
% 3.09/1.00  --pure_diseq_elim                       true
% 3.09/1.00  --brand_transform                       false
% 3.09/1.00  --non_eq_to_eq                          false
% 3.09/1.00  --prep_def_merge                        true
% 3.09/1.00  --prep_def_merge_prop_impl              false
% 3.09/1.00  --prep_def_merge_mbd                    true
% 3.09/1.00  --prep_def_merge_tr_red                 false
% 3.09/1.00  --prep_def_merge_tr_cl                  false
% 3.09/1.00  --smt_preprocessing                     true
% 3.09/1.00  --smt_ac_axioms                         fast
% 3.09/1.00  --preprocessed_out                      false
% 3.09/1.00  --preprocessed_stats                    false
% 3.09/1.00  
% 3.09/1.00  ------ Abstraction refinement Options
% 3.09/1.00  
% 3.09/1.00  --abstr_ref                             []
% 3.09/1.00  --abstr_ref_prep                        false
% 3.09/1.00  --abstr_ref_until_sat                   false
% 3.09/1.00  --abstr_ref_sig_restrict                funpre
% 3.09/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.00  --abstr_ref_under                       []
% 3.09/1.00  
% 3.09/1.00  ------ SAT Options
% 3.09/1.00  
% 3.09/1.00  --sat_mode                              false
% 3.09/1.00  --sat_fm_restart_options                ""
% 3.09/1.00  --sat_gr_def                            false
% 3.09/1.00  --sat_epr_types                         true
% 3.09/1.00  --sat_non_cyclic_types                  false
% 3.09/1.00  --sat_finite_models                     false
% 3.09/1.00  --sat_fm_lemmas                         false
% 3.09/1.00  --sat_fm_prep                           false
% 3.09/1.00  --sat_fm_uc_incr                        true
% 3.09/1.00  --sat_out_model                         small
% 3.09/1.00  --sat_out_clauses                       false
% 3.09/1.00  
% 3.09/1.00  ------ QBF Options
% 3.09/1.00  
% 3.09/1.00  --qbf_mode                              false
% 3.09/1.00  --qbf_elim_univ                         false
% 3.09/1.00  --qbf_dom_inst                          none
% 3.09/1.00  --qbf_dom_pre_inst                      false
% 3.09/1.00  --qbf_sk_in                             false
% 3.09/1.00  --qbf_pred_elim                         true
% 3.09/1.00  --qbf_split                             512
% 3.09/1.00  
% 3.09/1.00  ------ BMC1 Options
% 3.09/1.00  
% 3.09/1.00  --bmc1_incremental                      false
% 3.09/1.00  --bmc1_axioms                           reachable_all
% 3.09/1.00  --bmc1_min_bound                        0
% 3.09/1.00  --bmc1_max_bound                        -1
% 3.09/1.00  --bmc1_max_bound_default                -1
% 3.09/1.00  --bmc1_symbol_reachability              true
% 3.09/1.00  --bmc1_property_lemmas                  false
% 3.09/1.00  --bmc1_k_induction                      false
% 3.09/1.00  --bmc1_non_equiv_states                 false
% 3.09/1.00  --bmc1_deadlock                         false
% 3.09/1.00  --bmc1_ucm                              false
% 3.09/1.00  --bmc1_add_unsat_core                   none
% 3.09/1.00  --bmc1_unsat_core_children              false
% 3.09/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.00  --bmc1_out_stat                         full
% 3.09/1.00  --bmc1_ground_init                      false
% 3.09/1.00  --bmc1_pre_inst_next_state              false
% 3.09/1.00  --bmc1_pre_inst_state                   false
% 3.09/1.00  --bmc1_pre_inst_reach_state             false
% 3.09/1.00  --bmc1_out_unsat_core                   false
% 3.09/1.00  --bmc1_aig_witness_out                  false
% 3.09/1.00  --bmc1_verbose                          false
% 3.09/1.00  --bmc1_dump_clauses_tptp                false
% 3.09/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.00  --bmc1_dump_file                        -
% 3.09/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.00  --bmc1_ucm_extend_mode                  1
% 3.09/1.00  --bmc1_ucm_init_mode                    2
% 3.09/1.00  --bmc1_ucm_cone_mode                    none
% 3.09/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.00  --bmc1_ucm_relax_model                  4
% 3.09/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.00  --bmc1_ucm_layered_model                none
% 3.09/1.00  --bmc1_ucm_max_lemma_size               10
% 3.09/1.00  
% 3.09/1.00  ------ AIG Options
% 3.09/1.00  
% 3.09/1.00  --aig_mode                              false
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation Options
% 3.09/1.00  
% 3.09/1.00  --instantiation_flag                    true
% 3.09/1.00  --inst_sos_flag                         false
% 3.09/1.00  --inst_sos_phase                        true
% 3.09/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel_side                     none
% 3.09/1.00  --inst_solver_per_active                1400
% 3.09/1.00  --inst_solver_calls_frac                1.
% 3.09/1.00  --inst_passive_queue_type               priority_queues
% 3.09/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.01  --inst_passive_queues_freq              [25;2]
% 3.09/1.01  --inst_dismatching                      true
% 3.09/1.01  --inst_eager_unprocessed_to_passive     true
% 3.09/1.01  --inst_prop_sim_given                   true
% 3.09/1.01  --inst_prop_sim_new                     false
% 3.09/1.01  --inst_subs_new                         false
% 3.09/1.01  --inst_eq_res_simp                      false
% 3.09/1.01  --inst_subs_given                       false
% 3.09/1.01  --inst_orphan_elimination               true
% 3.09/1.01  --inst_learning_loop_flag               true
% 3.09/1.01  --inst_learning_start                   3000
% 3.09/1.01  --inst_learning_factor                  2
% 3.09/1.01  --inst_start_prop_sim_after_learn       3
% 3.09/1.01  --inst_sel_renew                        solver
% 3.09/1.01  --inst_lit_activity_flag                true
% 3.09/1.01  --inst_restr_to_given                   false
% 3.09/1.01  --inst_activity_threshold               500
% 3.09/1.01  --inst_out_proof                        true
% 3.09/1.01  
% 3.09/1.01  ------ Resolution Options
% 3.09/1.01  
% 3.09/1.01  --resolution_flag                       false
% 3.09/1.01  --res_lit_sel                           adaptive
% 3.09/1.01  --res_lit_sel_side                      none
% 3.09/1.01  --res_ordering                          kbo
% 3.09/1.01  --res_to_prop_solver                    active
% 3.09/1.01  --res_prop_simpl_new                    false
% 3.09/1.01  --res_prop_simpl_given                  true
% 3.09/1.01  --res_passive_queue_type                priority_queues
% 3.09/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.01  --res_passive_queues_freq               [15;5]
% 3.09/1.01  --res_forward_subs                      full
% 3.09/1.01  --res_backward_subs                     full
% 3.09/1.01  --res_forward_subs_resolution           true
% 3.09/1.01  --res_backward_subs_resolution          true
% 3.09/1.01  --res_orphan_elimination                true
% 3.09/1.01  --res_time_limit                        2.
% 3.09/1.01  --res_out_proof                         true
% 3.09/1.01  
% 3.09/1.01  ------ Superposition Options
% 3.09/1.01  
% 3.09/1.01  --superposition_flag                    true
% 3.09/1.01  --sup_passive_queue_type                priority_queues
% 3.09/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.01  --demod_completeness_check              fast
% 3.09/1.01  --demod_use_ground                      true
% 3.09/1.01  --sup_to_prop_solver                    passive
% 3.09/1.01  --sup_prop_simpl_new                    true
% 3.09/1.01  --sup_prop_simpl_given                  true
% 3.09/1.01  --sup_fun_splitting                     false
% 3.09/1.01  --sup_smt_interval                      50000
% 3.09/1.01  
% 3.09/1.01  ------ Superposition Simplification Setup
% 3.09/1.01  
% 3.09/1.01  --sup_indices_passive                   []
% 3.09/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_full_bw                           [BwDemod]
% 3.09/1.01  --sup_immed_triv                        [TrivRules]
% 3.09/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_immed_bw_main                     []
% 3.09/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.01  
% 3.09/1.01  ------ Combination Options
% 3.09/1.01  
% 3.09/1.01  --comb_res_mult                         3
% 3.09/1.01  --comb_sup_mult                         2
% 3.09/1.01  --comb_inst_mult                        10
% 3.09/1.01  
% 3.09/1.01  ------ Debug Options
% 3.09/1.01  
% 3.09/1.01  --dbg_backtrace                         false
% 3.09/1.01  --dbg_dump_prop_clauses                 false
% 3.09/1.01  --dbg_dump_prop_clauses_file            -
% 3.09/1.01  --dbg_out_stat                          false
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  ------ Proving...
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  % SZS status Theorem for theBenchmark.p
% 3.09/1.01  
% 3.09/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/1.01  
% 3.09/1.01  fof(f22,conjecture,(
% 3.09/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f23,negated_conjecture,(
% 3.09/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.09/1.01    inference(negated_conjecture,[],[f22])).
% 3.09/1.01  
% 3.09/1.01  fof(f45,plain,(
% 3.09/1.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.09/1.01    inference(ennf_transformation,[],[f23])).
% 3.09/1.01  
% 3.09/1.01  fof(f46,plain,(
% 3.09/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.09/1.01    inference(flattening,[],[f45])).
% 3.09/1.01  
% 3.09/1.01  fof(f53,plain,(
% 3.09/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.09/1.01    introduced(choice_axiom,[])).
% 3.09/1.01  
% 3.09/1.01  fof(f52,plain,(
% 3.09/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.09/1.01    introduced(choice_axiom,[])).
% 3.09/1.01  
% 3.09/1.01  fof(f54,plain,(
% 3.09/1.01    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.09/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f53,f52])).
% 3.09/1.01  
% 3.09/1.01  fof(f89,plain,(
% 3.09/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f92,plain,(
% 3.09/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f19,axiom,(
% 3.09/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f41,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.09/1.01    inference(ennf_transformation,[],[f19])).
% 3.09/1.01  
% 3.09/1.01  fof(f42,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.09/1.01    inference(flattening,[],[f41])).
% 3.09/1.01  
% 3.09/1.01  fof(f83,plain,(
% 3.09/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f42])).
% 3.09/1.01  
% 3.09/1.01  fof(f90,plain,(
% 3.09/1.01    v1_funct_1(sK3)),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f87,plain,(
% 3.09/1.01    v1_funct_1(sK2)),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f21,axiom,(
% 3.09/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f43,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.09/1.01    inference(ennf_transformation,[],[f21])).
% 3.09/1.01  
% 3.09/1.01  fof(f44,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.09/1.01    inference(flattening,[],[f43])).
% 3.09/1.01  
% 3.09/1.01  fof(f85,plain,(
% 3.09/1.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f44])).
% 3.09/1.01  
% 3.09/1.01  fof(f88,plain,(
% 3.09/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f91,plain,(
% 3.09/1.01    v1_funct_2(sK3,sK1,sK0)),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f13,axiom,(
% 3.09/1.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f74,plain,(
% 3.09/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f13])).
% 3.09/1.01  
% 3.09/1.01  fof(f20,axiom,(
% 3.09/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f84,plain,(
% 3.09/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f20])).
% 3.09/1.01  
% 3.09/1.01  fof(f97,plain,(
% 3.09/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.09/1.01    inference(definition_unfolding,[],[f74,f84])).
% 3.09/1.01  
% 3.09/1.01  fof(f7,axiom,(
% 3.09/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f29,plain,(
% 3.09/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.09/1.01    inference(ennf_transformation,[],[f7])).
% 3.09/1.01  
% 3.09/1.01  fof(f49,plain,(
% 3.09/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.09/1.01    inference(nnf_transformation,[],[f29])).
% 3.09/1.01  
% 3.09/1.01  fof(f64,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f49])).
% 3.09/1.01  
% 3.09/1.01  fof(f17,axiom,(
% 3.09/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f37,plain,(
% 3.09/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.09/1.01    inference(ennf_transformation,[],[f17])).
% 3.09/1.01  
% 3.09/1.01  fof(f38,plain,(
% 3.09/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.09/1.01    inference(flattening,[],[f37])).
% 3.09/1.01  
% 3.09/1.01  fof(f51,plain,(
% 3.09/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.09/1.01    inference(nnf_transformation,[],[f38])).
% 3.09/1.01  
% 3.09/1.01  fof(f80,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f51])).
% 3.09/1.01  
% 3.09/1.01  fof(f103,plain,(
% 3.09/1.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.09/1.01    inference(equality_resolution,[],[f80])).
% 3.09/1.01  
% 3.09/1.01  fof(f94,plain,(
% 3.09/1.01    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f2,axiom,(
% 3.09/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f47,plain,(
% 3.09/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.01    inference(nnf_transformation,[],[f2])).
% 3.09/1.01  
% 3.09/1.01  fof(f48,plain,(
% 3.09/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.01    inference(flattening,[],[f47])).
% 3.09/1.01  
% 3.09/1.01  fof(f57,plain,(
% 3.09/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.09/1.01    inference(cnf_transformation,[],[f48])).
% 3.09/1.01  
% 3.09/1.01  fof(f100,plain,(
% 3.09/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.09/1.01    inference(equality_resolution,[],[f57])).
% 3.09/1.01  
% 3.09/1.01  fof(f6,axiom,(
% 3.09/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f28,plain,(
% 3.09/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f6])).
% 3.09/1.01  
% 3.09/1.01  fof(f62,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f28])).
% 3.09/1.01  
% 3.09/1.01  fof(f8,axiom,(
% 3.09/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f65,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f8])).
% 3.09/1.01  
% 3.09/1.01  fof(f14,axiom,(
% 3.09/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f24,plain,(
% 3.09/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.09/1.01    inference(pure_predicate_removal,[],[f14])).
% 3.09/1.01  
% 3.09/1.01  fof(f34,plain,(
% 3.09/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(ennf_transformation,[],[f24])).
% 3.09/1.01  
% 3.09/1.01  fof(f75,plain,(
% 3.09/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f34])).
% 3.09/1.01  
% 3.09/1.01  fof(f63,plain,(
% 3.09/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f49])).
% 3.09/1.01  
% 3.09/1.01  fof(f58,plain,(
% 3.09/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f48])).
% 3.09/1.01  
% 3.09/1.01  fof(f15,axiom,(
% 3.09/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f35,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.09/1.01    inference(ennf_transformation,[],[f15])).
% 3.09/1.01  
% 3.09/1.01  fof(f36,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(flattening,[],[f35])).
% 3.09/1.01  
% 3.09/1.01  fof(f50,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.01    inference(nnf_transformation,[],[f36])).
% 3.09/1.01  
% 3.09/1.01  fof(f76,plain,(
% 3.09/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f50])).
% 3.09/1.01  
% 3.09/1.01  fof(f93,plain,(
% 3.09/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.09/1.01    inference(cnf_transformation,[],[f54])).
% 3.09/1.01  
% 3.09/1.01  fof(f16,axiom,(
% 3.09/1.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f78,plain,(
% 3.09/1.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.09/1.01    inference(cnf_transformation,[],[f16])).
% 3.09/1.01  
% 3.09/1.01  fof(f99,plain,(
% 3.09/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.09/1.01    inference(definition_unfolding,[],[f78,f84])).
% 3.09/1.01  
% 3.09/1.01  fof(f18,axiom,(
% 3.09/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f39,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.09/1.01    inference(ennf_transformation,[],[f18])).
% 3.09/1.01  
% 3.09/1.01  fof(f40,plain,(
% 3.09/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.09/1.01    inference(flattening,[],[f39])).
% 3.09/1.01  
% 3.09/1.01  fof(f82,plain,(
% 3.09/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f40])).
% 3.09/1.01  
% 3.09/1.01  fof(f9,axiom,(
% 3.09/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f30,plain,(
% 3.09/1.01    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f9])).
% 3.09/1.01  
% 3.09/1.01  fof(f66,plain,(
% 3.09/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f30])).
% 3.09/1.01  
% 3.09/1.01  fof(f10,axiom,(
% 3.09/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f68,plain,(
% 3.09/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.09/1.01    inference(cnf_transformation,[],[f10])).
% 3.09/1.01  
% 3.09/1.01  fof(f95,plain,(
% 3.09/1.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.09/1.01    inference(definition_unfolding,[],[f68,f84])).
% 3.09/1.01  
% 3.09/1.01  fof(f4,axiom,(
% 3.09/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f26,plain,(
% 3.09/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f4])).
% 3.09/1.01  
% 3.09/1.01  fof(f60,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f26])).
% 3.09/1.01  
% 3.09/1.01  fof(f1,axiom,(
% 3.09/1.01    v1_xboole_0(k1_xboole_0)),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f55,plain,(
% 3.09/1.01    v1_xboole_0(k1_xboole_0)),
% 3.09/1.01    inference(cnf_transformation,[],[f1])).
% 3.09/1.01  
% 3.09/1.01  fof(f3,axiom,(
% 3.09/1.01    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f25,plain,(
% 3.09/1.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f3])).
% 3.09/1.01  
% 3.09/1.01  fof(f59,plain,(
% 3.09/1.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f25])).
% 3.09/1.01  
% 3.09/1.01  fof(f12,axiom,(
% 3.09/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f32,plain,(
% 3.09/1.01    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 3.09/1.01    inference(ennf_transformation,[],[f12])).
% 3.09/1.01  
% 3.09/1.01  fof(f33,plain,(
% 3.09/1.01    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(flattening,[],[f32])).
% 3.09/1.01  
% 3.09/1.01  fof(f72,plain,(
% 3.09/1.01    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f33])).
% 3.09/1.01  
% 3.09/1.01  fof(f11,axiom,(
% 3.09/1.01    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f31,plain,(
% 3.09/1.01    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f11])).
% 3.09/1.01  
% 3.09/1.01  fof(f69,plain,(
% 3.09/1.01    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f31])).
% 3.09/1.01  
% 3.09/1.01  fof(f5,axiom,(
% 3.09/1.01    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.09/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.01  
% 3.09/1.01  fof(f27,plain,(
% 3.09/1.01    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.09/1.01    inference(ennf_transformation,[],[f5])).
% 3.09/1.01  
% 3.09/1.01  fof(f61,plain,(
% 3.09/1.01    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.09/1.01    inference(cnf_transformation,[],[f27])).
% 3.09/1.01  
% 3.09/1.01  cnf(c_36,negated_conjecture,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.09/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1219,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_33,negated_conjecture,
% 3.09/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.09/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1222,plain,
% 3.09/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_28,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(X3)
% 3.09/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1225,plain,
% 3.09/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.09/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.09/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.09/1.01      | v1_funct_1(X5) != iProver_top
% 3.09/1.01      | v1_funct_1(X4) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3683,plain,
% 3.09/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.09/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.09/1.01      | v1_funct_1(X2) != iProver_top
% 3.09/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1222,c_1225]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_35,negated_conjecture,
% 3.09/1.01      ( v1_funct_1(sK3) ),
% 3.09/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_42,plain,
% 3.09/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3719,plain,
% 3.09/1.01      ( v1_funct_1(X2) != iProver_top
% 3.09/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.09/1.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_3683,c_42]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3720,plain,
% 3.09/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.09/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.09/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.09/1.01      inference(renaming,[status(thm)],[c_3719]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3730,plain,
% 3.09/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.09/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1219,c_3720]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_38,negated_conjecture,
% 3.09/1.01      ( v1_funct_1(sK2) ),
% 3.09/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1570,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(sK3)
% 3.09/1.01      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1839,plain,
% 3.09/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.09/1.01      | ~ v1_funct_1(sK2)
% 3.09/1.01      | ~ v1_funct_1(sK3)
% 3.09/1.01      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1570]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2303,plain,
% 3.09/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.09/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.01      | ~ v1_funct_1(sK2)
% 3.09/1.01      | ~ v1_funct_1(sK3)
% 3.09/1.01      | k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1839]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3599,plain,
% 3.09/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.09/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.09/1.01      | ~ v1_funct_1(sK2)
% 3.09/1.01      | ~ v1_funct_1(sK3)
% 3.09/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_2303]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3767,plain,
% 3.09/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_3730,c_38,c_36,c_35,c_33,c_3599]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_30,plain,
% 3.09/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.09/1.01      | ~ v1_funct_2(X3,X4,X1)
% 3.09/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.09/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | v2_funct_1(X3)
% 3.09/1.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(X3)
% 3.09/1.01      | k1_xboole_0 = X2 ),
% 3.09/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1223,plain,
% 3.09/1.01      ( k1_xboole_0 = X0
% 3.09/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.09/1.01      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.09/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.09/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.09/1.01      | v2_funct_1(X3) = iProver_top
% 3.09/1.01      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
% 3.09/1.01      | v1_funct_1(X1) != iProver_top
% 3.09/1.01      | v1_funct_1(X3) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3773,plain,
% 3.09/1.01      ( sK0 = k1_xboole_0
% 3.09/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.09/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.09/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.09/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.09/1.01      | v2_funct_1(sK2) = iProver_top
% 3.09/1.01      | v1_funct_1(sK2) != iProver_top
% 3.09/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_3767,c_1223]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_39,plain,
% 3.09/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_37,negated_conjecture,
% 3.09/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.09/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_40,plain,
% 3.09/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_41,plain,
% 3.09/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_34,negated_conjecture,
% 3.09/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_43,plain,
% 3.09/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_44,plain,
% 3.09/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_18,plain,
% 3.09/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_83,plain,
% 3.09/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_85,plain,
% 3.09/1.01      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_83]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_8,plain,
% 3.09/1.01      ( v5_relat_1(X0,X1)
% 3.09/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.09/1.01      | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_24,plain,
% 3.09/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.09/1.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.09/1.01      | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_31,negated_conjecture,
% 3.09/1.01      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.09/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_422,plain,
% 3.09/1.01      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.09/1.01      | ~ v2_funct_1(sK2)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | k2_relat_1(X0) != sK0
% 3.09/1.01      | sK3 != X0 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_423,plain,
% 3.09/1.01      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.09/1.01      | ~ v2_funct_1(sK2)
% 3.09/1.01      | ~ v1_relat_1(sK3)
% 3.09/1.01      | k2_relat_1(sK3) != sK0 ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_422]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_476,plain,
% 3.09/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.09/1.01      | ~ v2_funct_1(sK2)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | ~ v1_relat_1(sK3)
% 3.09/1.01      | k2_relat_1(sK3) != X1
% 3.09/1.01      | k2_relat_1(sK3) != sK0
% 3.09/1.01      | sK3 != X0 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_423]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_477,plain,
% 3.09/1.01      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.09/1.01      | ~ v2_funct_1(sK2)
% 3.09/1.01      | ~ v1_relat_1(sK3)
% 3.09/1.01      | k2_relat_1(sK3) != sK0 ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_476]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2,plain,
% 3.09/1.01      ( r1_tarski(X0,X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_487,plain,
% 3.09/1.01      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.09/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_477,c_2]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_488,plain,
% 3.09/1.01      ( k2_relat_1(sK3) != sK0
% 3.09/1.01      | v2_funct_1(sK2) != iProver_top
% 3.09/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_7,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.09/1.01      | ~ v1_relat_1(X1)
% 3.09/1.01      | v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1234,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.09/1.01      | v1_relat_1(X1) != iProver_top
% 3.09/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2815,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.09/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1222,c_1234]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_10,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1233,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2981,plain,
% 3.09/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 3.09/1.01      inference(forward_subsumption_resolution,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_2815,c_1233]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2816,plain,
% 3.09/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.09/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1219,c_1234]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2986,plain,
% 3.09/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.09/1.01      inference(forward_subsumption_resolution,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_2816,c_1233]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_20,plain,
% 3.09/1.01      ( v5_relat_1(X0,X1)
% 3.09/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.09/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_9,plain,
% 3.09/1.01      ( ~ v5_relat_1(X0,X1)
% 3.09/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 3.09/1.01      | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_443,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.09/1.01      | ~ v1_relat_1(X0) ),
% 3.09/1.01      inference(resolution,[status(thm)],[c_20,c_9]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1214,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.09/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.09/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2648,plain,
% 3.09/1.01      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.09/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1222,c_1214]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1,plain,
% 3.09/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.09/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1239,plain,
% 3.09/1.01      ( X0 = X1
% 3.09/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.09/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2929,plain,
% 3.09/1.01      ( k2_relat_1(sK3) = sK0
% 3.09/1.01      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.09/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_2648,c_1239]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3919,plain,
% 3.09/1.01      ( r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.09/1.01      | k2_relat_1(sK3) = sK0 ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_2929,c_2981]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3920,plain,
% 3.09/1.01      ( k2_relat_1(sK3) = sK0
% 3.09/1.01      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 3.09/1.01      inference(renaming,[status(thm)],[c_3919]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_22,plain,
% 3.09/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.09/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.01      | X3 = X2 ),
% 3.09/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_32,negated_conjecture,
% 3.09/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_403,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | X3 = X0
% 3.09/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.09/1.01      | k6_partfun1(sK0) != X3
% 3.09/1.01      | sK0 != X2
% 3.09/1.01      | sK0 != X1 ),
% 3.09/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_404,plain,
% 3.09/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.09/1.01      inference(unflattening,[status(thm)],[c_403]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_23,plain,
% 3.09/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.09/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_69,plain,
% 3.09/1.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_406,plain,
% 3.09/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_404,c_69]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1215,plain,
% 3.09/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.09/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3770,plain,
% 3.09/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.09/1.01      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_3767,c_1215]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_26,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.09/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(X3) ),
% 3.09/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1227,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.09/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.09/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.09/1.01      | v1_funct_1(X0) != iProver_top
% 3.09/1.01      | v1_funct_1(X3) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4095,plain,
% 3.09/1.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.09/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.09/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v1_funct_1(sK2) != iProver_top
% 3.09/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_3767,c_1227]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4336,plain,
% 3.09/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_3770,c_39,c_41,c_42,c_44,c_4095]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_11,plain,
% 3.09/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X1) ),
% 3.09/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1232,plain,
% 3.09/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.09/1.01      | v1_relat_1(X0) != iProver_top
% 3.09/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4340,plain,
% 3.09/1.01      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.09/1.01      | v1_relat_1(sK2) != iProver_top
% 3.09/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_4336,c_1232]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_12,plain,
% 3.09/1.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.09/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4341,plain,
% 3.09/1.01      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.09/1.01      | v1_relat_1(sK2) != iProver_top
% 3.09/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4340,c_12]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4339,plain,
% 3.09/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_4336,c_3767]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4541,plain,
% 3.09/1.01      ( sK0 = k1_xboole_0
% 3.09/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.09/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.09/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.09/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.09/1.01      | v2_funct_1(sK2) = iProver_top
% 3.09/1.01      | v1_funct_1(sK2) != iProver_top
% 3.09/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_4339,c_1223]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_8284,plain,
% 3.09/1.01      ( sK0 = k1_xboole_0 ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_3773,c_39,c_40,c_41,c_42,c_43,c_44,c_85,c_488,c_2929,
% 3.09/1.01                 c_2981,c_2986,c_4341,c_4541]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_5,plain,
% 3.09/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.09/1.01      | ~ v1_xboole_0(X1)
% 3.09/1.01      | v1_xboole_0(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1236,plain,
% 3.09/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.09/1.01      | v1_xboole_0(X1) != iProver_top
% 3.09/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_2833,plain,
% 3.09/1.01      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.09/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1219,c_1236]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_8321,plain,
% 3.09/1.01      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top
% 3.09/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(demodulation,[status(thm)],[c_8284,c_2833]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_0,plain,
% 3.09/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_123,plain,
% 3.09/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_692,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.09/1.01      theory(equality) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1593,plain,
% 3.09/1.01      ( v1_xboole_0(X0)
% 3.09/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.09/1.01      | X0 != k1_xboole_0 ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_692]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1594,plain,
% 3.09/1.01      ( X0 != k1_xboole_0
% 3.09/1.01      | v1_xboole_0(X0) = iProver_top
% 3.09/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_1593]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1596,plain,
% 3.09/1.01      ( sK0 != k1_xboole_0
% 3.09/1.01      | v1_xboole_0(sK0) = iProver_top
% 3.09/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.09/1.01      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_4,plain,
% 3.09/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.09/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1237,plain,
% 3.09/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.09/1.01      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_3130,plain,
% 3.09/1.01      ( v1_xboole_0(sK2) = iProver_top
% 3.09/1.01      | v1_xboole_0(sK0) != iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_1237,c_2833]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_9312,plain,
% 3.09/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_8321,c_39,c_40,c_41,c_42,c_43,c_44,c_85,c_123,c_488,
% 3.09/1.01                 c_1596,c_2929,c_2981,c_2986,c_3130,c_4341,c_4541]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_15,plain,
% 3.09/1.01      ( v2_funct_1(X0)
% 3.09/1.01      | ~ v1_funct_1(X0)
% 3.09/1.01      | ~ v1_relat_1(X0)
% 3.09/1.01      | ~ v1_xboole_0(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_14,plain,
% 3.09/1.01      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_6,plain,
% 3.09/1.01      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.09/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_220,plain,
% 3.09/1.01      ( v2_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.09/1.01      inference(global_propositional_subsumption,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_15,c_14,c_6]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_1216,plain,
% 3.09/1.01      ( v2_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.09/1.01      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(c_9319,plain,
% 3.09/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 3.09/1.01      inference(superposition,[status(thm)],[c_9312,c_1216]) ).
% 3.09/1.01  
% 3.09/1.01  cnf(contradiction,plain,
% 3.09/1.01      ( $false ),
% 3.09/1.01      inference(minisat,
% 3.09/1.01                [status(thm)],
% 3.09/1.01                [c_9319,c_4341,c_3920,c_2986,c_2981,c_488]) ).
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/1.01  
% 3.09/1.01  ------                               Statistics
% 3.09/1.01  
% 3.09/1.01  ------ General
% 3.09/1.01  
% 3.09/1.01  abstr_ref_over_cycles:                  0
% 3.09/1.01  abstr_ref_under_cycles:                 0
% 3.09/1.01  gc_basic_clause_elim:                   0
% 3.09/1.01  forced_gc_time:                         0
% 3.09/1.01  parsing_time:                           0.01
% 3.09/1.01  unif_index_cands_time:                  0.
% 3.09/1.01  unif_index_add_time:                    0.
% 3.09/1.01  orderings_time:                         0.
% 3.09/1.01  out_proof_time:                         0.012
% 3.09/1.01  total_time:                             0.355
% 3.09/1.01  num_of_symbols:                         53
% 3.09/1.01  num_of_terms:                           13346
% 3.09/1.01  
% 3.09/1.01  ------ Preprocessing
% 3.09/1.01  
% 3.09/1.01  num_of_splits:                          0
% 3.09/1.01  num_of_split_atoms:                     0
% 3.09/1.01  num_of_reused_defs:                     0
% 3.09/1.01  num_eq_ax_congr_red:                    7
% 3.09/1.01  num_of_sem_filtered_clauses:            1
% 3.09/1.01  num_of_subtypes:                        0
% 3.09/1.01  monotx_restored_types:                  0
% 3.09/1.01  sat_num_of_epr_types:                   0
% 3.09/1.01  sat_num_of_non_cyclic_types:            0
% 3.09/1.01  sat_guarded_non_collapsed_types:        0
% 3.09/1.01  num_pure_diseq_elim:                    0
% 3.09/1.01  simp_replaced_by:                       0
% 3.09/1.01  res_preprocessed:                       157
% 3.09/1.01  prep_upred:                             0
% 3.09/1.01  prep_unflattend:                        15
% 3.09/1.01  smt_new_axioms:                         0
% 3.09/1.01  pred_elim_cands:                        7
% 3.09/1.01  pred_elim:                              3
% 3.09/1.01  pred_elim_cl:                           6
% 3.09/1.01  pred_elim_cycles:                       5
% 3.09/1.01  merged_defs:                            0
% 3.09/1.01  merged_defs_ncl:                        0
% 3.09/1.01  bin_hyper_res:                          0
% 3.09/1.01  prep_cycles:                            4
% 3.09/1.01  pred_elim_time:                         0.002
% 3.09/1.01  splitting_time:                         0.
% 3.09/1.01  sem_filter_time:                        0.
% 3.09/1.01  monotx_time:                            0.
% 3.09/1.01  subtype_inf_time:                       0.
% 3.09/1.01  
% 3.09/1.01  ------ Problem properties
% 3.09/1.01  
% 3.09/1.01  clauses:                                30
% 3.09/1.01  conjectures:                            6
% 3.09/1.01  epr:                                    10
% 3.09/1.01  horn:                                   29
% 3.09/1.01  ground:                                 9
% 3.09/1.01  unary:                                  14
% 3.09/1.01  binary:                                 5
% 3.09/1.01  lits:                                   74
% 3.09/1.01  lits_eq:                                7
% 3.09/1.01  fd_pure:                                0
% 3.09/1.01  fd_pseudo:                              0
% 3.09/1.01  fd_cond:                                1
% 3.09/1.01  fd_pseudo_cond:                         1
% 3.09/1.01  ac_symbols:                             0
% 3.09/1.01  
% 3.09/1.01  ------ Propositional Solver
% 3.09/1.01  
% 3.09/1.01  prop_solver_calls:                      27
% 3.09/1.01  prop_fast_solver_calls:                 1168
% 3.09/1.01  smt_solver_calls:                       0
% 3.09/1.01  smt_fast_solver_calls:                  0
% 3.09/1.01  prop_num_of_clauses:                    4346
% 3.09/1.01  prop_preprocess_simplified:             10530
% 3.09/1.01  prop_fo_subsumed:                       60
% 3.09/1.01  prop_solver_time:                       0.
% 3.09/1.01  smt_solver_time:                        0.
% 3.09/1.01  smt_fast_solver_time:                   0.
% 3.09/1.01  prop_fast_solver_time:                  0.
% 3.09/1.01  prop_unsat_core_time:                   0.
% 3.09/1.01  
% 3.09/1.01  ------ QBF
% 3.09/1.01  
% 3.09/1.01  qbf_q_res:                              0
% 3.09/1.01  qbf_num_tautologies:                    0
% 3.09/1.01  qbf_prep_cycles:                        0
% 3.09/1.01  
% 3.09/1.01  ------ BMC1
% 3.09/1.01  
% 3.09/1.01  bmc1_current_bound:                     -1
% 3.09/1.01  bmc1_last_solved_bound:                 -1
% 3.09/1.01  bmc1_unsat_core_size:                   -1
% 3.09/1.01  bmc1_unsat_core_parents_size:           -1
% 3.09/1.01  bmc1_merge_next_fun:                    0
% 3.09/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.09/1.01  
% 3.09/1.01  ------ Instantiation
% 3.09/1.01  
% 3.09/1.01  inst_num_of_clauses:                    1094
% 3.09/1.01  inst_num_in_passive:                    300
% 3.09/1.01  inst_num_in_active:                     484
% 3.09/1.01  inst_num_in_unprocessed:                310
% 3.09/1.01  inst_num_of_loops:                      530
% 3.09/1.01  inst_num_of_learning_restarts:          0
% 3.09/1.01  inst_num_moves_active_passive:          45
% 3.09/1.01  inst_lit_activity:                      0
% 3.09/1.01  inst_lit_activity_moves:                0
% 3.09/1.01  inst_num_tautologies:                   0
% 3.09/1.01  inst_num_prop_implied:                  0
% 3.09/1.01  inst_num_existing_simplified:           0
% 3.09/1.01  inst_num_eq_res_simplified:             0
% 3.09/1.01  inst_num_child_elim:                    0
% 3.09/1.01  inst_num_of_dismatching_blockings:      79
% 3.09/1.01  inst_num_of_non_proper_insts:           739
% 3.09/1.01  inst_num_of_duplicates:                 0
% 3.09/1.01  inst_inst_num_from_inst_to_res:         0
% 3.09/1.01  inst_dismatching_checking_time:         0.
% 3.09/1.01  
% 3.09/1.01  ------ Resolution
% 3.09/1.01  
% 3.09/1.01  res_num_of_clauses:                     0
% 3.09/1.01  res_num_in_passive:                     0
% 3.09/1.01  res_num_in_active:                      0
% 3.09/1.01  res_num_of_loops:                       161
% 3.09/1.01  res_forward_subset_subsumed:            36
% 3.09/1.01  res_backward_subset_subsumed:           0
% 3.09/1.01  res_forward_subsumed:                   0
% 3.09/1.01  res_backward_subsumed:                  1
% 3.09/1.01  res_forward_subsumption_resolution:     1
% 3.09/1.01  res_backward_subsumption_resolution:    0
% 3.09/1.01  res_clause_to_clause_subsumption:       465
% 3.09/1.01  res_orphan_elimination:                 0
% 3.09/1.01  res_tautology_del:                      21
% 3.09/1.01  res_num_eq_res_simplified:              0
% 3.09/1.01  res_num_sel_changes:                    0
% 3.09/1.01  res_moves_from_active_to_pass:          0
% 3.09/1.01  
% 3.09/1.01  ------ Superposition
% 3.09/1.01  
% 3.09/1.01  sup_time_total:                         0.
% 3.09/1.01  sup_time_generating:                    0.
% 3.09/1.01  sup_time_sim_full:                      0.
% 3.09/1.01  sup_time_sim_immed:                     0.
% 3.09/1.01  
% 3.09/1.01  sup_num_of_clauses:                     179
% 3.09/1.01  sup_num_in_active:                      57
% 3.09/1.01  sup_num_in_passive:                     122
% 3.09/1.01  sup_num_of_loops:                       104
% 3.09/1.01  sup_fw_superposition:                   99
% 3.09/1.01  sup_bw_superposition:                   97
% 3.09/1.01  sup_immediate_simplified:               45
% 3.09/1.01  sup_given_eliminated:                   1
% 3.09/1.01  comparisons_done:                       0
% 3.09/1.01  comparisons_avoided:                    0
% 3.09/1.01  
% 3.09/1.01  ------ Simplifications
% 3.09/1.01  
% 3.09/1.01  
% 3.09/1.01  sim_fw_subset_subsumed:                 20
% 3.09/1.01  sim_bw_subset_subsumed:                 9
% 3.09/1.01  sim_fw_subsumed:                        4
% 3.09/1.01  sim_bw_subsumed:                        1
% 3.09/1.01  sim_fw_subsumption_res:                 6
% 3.09/1.01  sim_bw_subsumption_res:                 0
% 3.09/1.01  sim_tautology_del:                      0
% 3.09/1.01  sim_eq_tautology_del:                   7
% 3.09/1.01  sim_eq_res_simp:                        0
% 3.09/1.01  sim_fw_demodulated:                     1
% 3.09/1.01  sim_bw_demodulated:                     45
% 3.09/1.01  sim_light_normalised:                   23
% 3.09/1.01  sim_joinable_taut:                      0
% 3.09/1.01  sim_joinable_simp:                      0
% 3.09/1.01  sim_ac_normalised:                      0
% 3.09/1.01  sim_smt_subsumption:                    0
% 3.09/1.01  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:02:00 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 752 expanded)
%              Number of clauses        :  106 ( 243 expanded)
%              Number of leaves         :   26 ( 172 expanded)
%              Depth                    :   21
%              Number of atoms          :  646 (3872 expanded)
%              Number of equality atoms :  194 ( 391 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

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

fof(f44,plain,(
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
    inference(flattening,[],[f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK5,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK5,X1,X0)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
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
          ( ( ~ v2_funct_2(X3,sK2)
            | ~ v2_funct_1(sK4) )
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
          & v1_funct_2(X3,sK3,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ~ v2_funct_2(sK5,sK2)
      | ~ v2_funct_1(sK4) )
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f45,f61,f60])).

fof(f102,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f87,f92])).

fof(f96,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f101,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f42,plain,(
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
    inference(flattening,[],[f42])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f111,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f103,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f20,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f80,f92])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f106,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f79,f92])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f57,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(rectify,[],[f24])).

fof(f75,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f104,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f78,f92])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1949,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
    | k6_partfun1(sK2) != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_718,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_726,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_718,c_24])).

cnf(c_1927,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_5171,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1949,c_1927])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5810,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5171,c_40,c_42,c_43,c_45])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1946,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5836,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5810,c_1946])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_44,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_25,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_32,negated_conjecture,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_413,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_414,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_587,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_414])).

cnf(c_588,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_598,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_588,c_6])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK4)
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_598])).

cnf(c_630,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK4)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_1272,plain,
    ( ~ v2_funct_1(sK4)
    | sP3_iProver_split
    | k2_relat_1(sK5) != sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_630])).

cnf(c_1322,plain,
    ( k2_relat_1(sK5) != sK2
    | v2_funct_1(sK4) != iProver_top
    | sP3_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_1945,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1271,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_630])).

cnf(c_1935,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_2598,plain,
    ( sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_1935])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1951,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3837,plain,
    ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1945,c_1951])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_730,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_731,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ v1_funct_2(X2,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK2,X1,X1,sK2,X2,X0) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | k2_relset_1(X1,sK2,X0) = sK2
    | k6_partfun1(sK2) != k6_partfun1(sK2) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_817,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ v1_funct_2(X2,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK2,X1,X1,sK2,X2,X0) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | k2_relset_1(X1,sK2,X0) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_731])).

cnf(c_1926,plain,
    ( k1_partfun1(sK2,X0,X0,sK2,X1,X2) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | k2_relset_1(X0,sK2,X2) = sK2
    | v1_funct_2(X2,X0,sK2) != iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_2369,plain,
    ( k2_relset_1(sK3,sK2,sK5) = sK2
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1926])).

cnf(c_2556,plain,
    ( k2_relset_1(sK3,sK2,sK5) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2369,c_40,c_41,c_42,c_43,c_44,c_45])).

cnf(c_3846,plain,
    ( k2_relat_1(sK5) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3837,c_2556])).

cnf(c_6714,plain,
    ( v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5836,c_40,c_41,c_42,c_43,c_44,c_45,c_1322,c_2598,c_3846])).

cnf(c_6715,plain,
    ( sK2 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6714])).

cnf(c_16,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1953,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6720,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6715,c_1953])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1959,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1955,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1942,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1954,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4843,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_1954])).

cnf(c_4888,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_4843])).

cnf(c_5020,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_4888])).

cnf(c_17,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( v5_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_555,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_556,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_1021,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | k6_partfun1(X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_556])).

cnf(c_1269,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_1021])).

cnf(c_1932,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2003,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1932,c_13])).

cnf(c_15,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1270,plain,
    ( sP2_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1021])).

cnf(c_1315,plain,
    ( sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_1268,plain,
    ( k6_partfun1(X0) != k1_xboole_0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1021])).

cnf(c_1319,plain,
    ( k6_partfun1(X0) != k1_xboole_0
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_1321,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_2951,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2003,c_15,c_1315,c_1321])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1957,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4718,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_1957])).

cnf(c_5601,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5020,c_4718])).

cnf(c_2455,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1953])).

cnf(c_2456,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2455])).

cnf(c_2599,plain,
    ( ~ sP3_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2598])).

cnf(c_1287,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2605,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_2607,plain,
    ( v2_funct_1(sK4)
    | ~ v2_funct_1(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2605])).

cnf(c_6632,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5601,c_1272,c_2456,c_2599,c_2607,c_3846])).

cnf(c_6722,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6720,c_6632])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1962,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1952,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3481,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_1952])).

cnf(c_3552,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_3481])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6722,c_3552])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.97/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.98  
% 2.97/0.98  ------  iProver source info
% 2.97/0.98  
% 2.97/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.98  git: non_committed_changes: false
% 2.97/0.98  git: last_make_outside_of_git: false
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     num_symb
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       true
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  ------ Parsing...
% 2.97/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.98  ------ Proving...
% 2.97/0.98  ------ Problem Properties 
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  clauses                                 40
% 2.97/0.98  conjectures                             6
% 2.97/0.98  EPR                                     11
% 2.97/0.98  Horn                                    35
% 2.97/0.98  unary                                   12
% 2.97/0.98  binary                                  17
% 2.97/0.98  lits                                    104
% 2.97/0.98  lits eq                                 15
% 2.97/0.98  fd_pure                                 0
% 2.97/0.98  fd_pseudo                               0
% 2.97/0.98  fd_cond                                 1
% 2.97/0.98  fd_pseudo_cond                          1
% 2.97/0.98  AC symbols                              0
% 2.97/0.98  
% 2.97/0.98  ------ Schedule dynamic 5 is on 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  Current options:
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     none
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       false
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ Proving...
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  % SZS status Theorem for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  fof(f18,axiom,(
% 2.97/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f38,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.97/0.98    inference(ennf_transformation,[],[f18])).
% 2.97/0.98  
% 2.97/0.98  fof(f39,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.97/0.98    inference(flattening,[],[f38])).
% 2.97/0.98  
% 2.97/0.98  fof(f91,plain,(
% 2.97/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f39])).
% 2.97/0.98  
% 2.97/0.98  fof(f15,axiom,(
% 2.97/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f34,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.97/0.98    inference(ennf_transformation,[],[f15])).
% 2.97/0.98  
% 2.97/0.98  fof(f35,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(flattening,[],[f34])).
% 2.97/0.98  
% 2.97/0.98  fof(f58,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(nnf_transformation,[],[f35])).
% 2.97/0.98  
% 2.97/0.98  fof(f85,plain,(
% 2.97/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f58])).
% 2.97/0.98  
% 2.97/0.98  fof(f22,conjecture,(
% 2.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f23,negated_conjecture,(
% 2.97/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.97/0.98    inference(negated_conjecture,[],[f22])).
% 2.97/0.98  
% 2.97/0.98  fof(f44,plain,(
% 2.97/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.97/0.98    inference(ennf_transformation,[],[f23])).
% 2.97/0.98  
% 2.97/0.98  fof(f45,plain,(
% 2.97/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.97/0.98    inference(flattening,[],[f44])).
% 2.97/0.98  
% 2.97/0.98  fof(f61,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f60,plain,(
% 2.97/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f62,plain,(
% 2.97/0.98    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f45,f61,f60])).
% 2.97/0.98  
% 2.97/0.98  fof(f102,plain,(
% 2.97/0.98    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f16,axiom,(
% 2.97/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f87,plain,(
% 2.97/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f16])).
% 2.97/0.98  
% 2.97/0.98  fof(f19,axiom,(
% 2.97/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f92,plain,(
% 2.97/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f19])).
% 2.97/0.98  
% 2.97/0.98  fof(f107,plain,(
% 2.97/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.97/0.98    inference(definition_unfolding,[],[f87,f92])).
% 2.97/0.98  
% 2.97/0.98  fof(f96,plain,(
% 2.97/0.98    v1_funct_1(sK4)),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f98,plain,(
% 2.97/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f99,plain,(
% 2.97/0.98    v1_funct_1(sK5)),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f101,plain,(
% 2.97/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f21,axiom,(
% 2.97/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f42,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.97/0.98    inference(ennf_transformation,[],[f21])).
% 2.97/0.98  
% 2.97/0.98  fof(f43,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.97/0.98    inference(flattening,[],[f42])).
% 2.97/0.98  
% 2.97/0.98  fof(f94,plain,(
% 2.97/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f43])).
% 2.97/0.98  
% 2.97/0.98  fof(f97,plain,(
% 2.97/0.98    v1_funct_2(sK4,sK2,sK3)),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f100,plain,(
% 2.97/0.98    v1_funct_2(sK5,sK3,sK2)),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f12,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f31,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f12])).
% 2.97/0.98  
% 2.97/0.98  fof(f82,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f31])).
% 2.97/0.98  
% 2.97/0.98  fof(f6,axiom,(
% 2.97/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f29,plain,(
% 2.97/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.97/0.98    inference(ennf_transformation,[],[f6])).
% 2.97/0.98  
% 2.97/0.98  fof(f56,plain,(
% 2.97/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.97/0.98    inference(nnf_transformation,[],[f29])).
% 2.97/0.98  
% 2.97/0.98  fof(f74,plain,(
% 2.97/0.98    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f56])).
% 2.97/0.98  
% 2.97/0.98  fof(f17,axiom,(
% 2.97/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f36,plain,(
% 2.97/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.97/0.98    inference(ennf_transformation,[],[f17])).
% 2.97/0.98  
% 2.97/0.98  fof(f37,plain,(
% 2.97/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/0.98    inference(flattening,[],[f36])).
% 2.97/0.98  
% 2.97/0.98  fof(f59,plain,(
% 2.97/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/0.98    inference(nnf_transformation,[],[f37])).
% 2.97/0.98  
% 2.97/0.98  fof(f89,plain,(
% 2.97/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f59])).
% 2.97/0.98  
% 2.97/0.98  fof(f111,plain,(
% 2.97/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.97/0.98    inference(equality_resolution,[],[f89])).
% 2.97/0.98  
% 2.97/0.98  fof(f103,plain,(
% 2.97/0.98    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 2.97/0.98    inference(cnf_transformation,[],[f62])).
% 2.97/0.98  
% 2.97/0.98  fof(f3,axiom,(
% 2.97/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f54,plain,(
% 2.97/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.98    inference(nnf_transformation,[],[f3])).
% 2.97/0.98  
% 2.97/0.98  fof(f55,plain,(
% 2.97/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/0.98    inference(flattening,[],[f54])).
% 2.97/0.98  
% 2.97/0.98  fof(f69,plain,(
% 2.97/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.97/0.98    inference(cnf_transformation,[],[f55])).
% 2.97/0.98  
% 2.97/0.98  fof(f108,plain,(
% 2.97/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.97/0.98    inference(equality_resolution,[],[f69])).
% 2.97/0.98  
% 2.97/0.98  fof(f14,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f33,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f14])).
% 2.97/0.98  
% 2.97/0.98  fof(f84,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f33])).
% 2.97/0.98  
% 2.97/0.98  fof(f20,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f40,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.97/0.98    inference(ennf_transformation,[],[f20])).
% 2.97/0.98  
% 2.97/0.98  fof(f41,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.97/0.98    inference(flattening,[],[f40])).
% 2.97/0.98  
% 2.97/0.98  fof(f93,plain,(
% 2.97/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f41])).
% 2.97/0.98  
% 2.97/0.98  fof(f10,axiom,(
% 2.97/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f80,plain,(
% 2.97/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f10])).
% 2.97/0.98  
% 2.97/0.98  fof(f105,plain,(
% 2.97/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.97/0.98    inference(definition_unfolding,[],[f80,f92])).
% 2.97/0.98  
% 2.97/0.98  fof(f2,axiom,(
% 2.97/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f26,plain,(
% 2.97/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.97/0.98    inference(ennf_transformation,[],[f2])).
% 2.97/0.98  
% 2.97/0.98  fof(f50,plain,(
% 2.97/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.98    inference(nnf_transformation,[],[f26])).
% 2.97/0.98  
% 2.97/0.98  fof(f51,plain,(
% 2.97/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.98    inference(rectify,[],[f50])).
% 2.97/0.98  
% 2.97/0.98  fof(f52,plain,(
% 2.97/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f53,plain,(
% 2.97/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).
% 2.97/0.98  
% 2.97/0.98  fof(f66,plain,(
% 2.97/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f53])).
% 2.97/0.98  
% 2.97/0.98  fof(f4,axiom,(
% 2.97/0.98    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f27,plain,(
% 2.97/0.98    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.97/0.98    inference(ennf_transformation,[],[f4])).
% 2.97/0.98  
% 2.97/0.98  fof(f71,plain,(
% 2.97/0.98    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f27])).
% 2.97/0.98  
% 2.97/0.98  fof(f5,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f28,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.97/0.98    inference(ennf_transformation,[],[f5])).
% 2.97/0.98  
% 2.97/0.98  fof(f72,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f28])).
% 2.97/0.98  
% 2.97/0.98  fof(f79,plain,(
% 2.97/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f10])).
% 2.97/0.98  
% 2.97/0.98  fof(f106,plain,(
% 2.97/0.98    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.97/0.98    inference(definition_unfolding,[],[f79,f92])).
% 2.97/0.98  
% 2.97/0.98  fof(f73,plain,(
% 2.97/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f56])).
% 2.97/0.98  
% 2.97/0.98  fof(f7,axiom,(
% 2.97/0.98    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f24,plain,(
% 2.97/0.98    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 2.97/0.98    inference(pure_predicate_removal,[],[f7])).
% 2.97/0.98  
% 2.97/0.98  fof(f57,plain,(
% 2.97/0.98    ! [X1] : v5_relat_1(k1_xboole_0,X1)),
% 2.97/0.98    inference(rectify,[],[f24])).
% 2.97/0.98  
% 2.97/0.98  fof(f75,plain,(
% 2.97/0.98    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f57])).
% 2.97/0.98  
% 2.97/0.98  fof(f8,axiom,(
% 2.97/0.98    k2_relat_1(k1_xboole_0) = k1_xboole_0 & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f77,plain,(
% 2.97/0.98    k2_relat_1(k1_xboole_0) = k1_xboole_0),
% 2.97/0.98    inference(cnf_transformation,[],[f8])).
% 2.97/0.98  
% 2.97/0.98  fof(f9,axiom,(
% 2.97/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f78,plain,(
% 2.97/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.97/0.98    inference(cnf_transformation,[],[f9])).
% 2.97/0.98  
% 2.97/0.98  fof(f104,plain,(
% 2.97/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.97/0.98    inference(definition_unfolding,[],[f78,f92])).
% 2.97/0.98  
% 2.97/0.98  fof(f70,plain,(
% 2.97/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f55])).
% 2.97/0.98  
% 2.97/0.98  fof(f1,axiom,(
% 2.97/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f46,plain,(
% 2.97/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.97/0.98    inference(nnf_transformation,[],[f1])).
% 2.97/0.98  
% 2.97/0.98  fof(f47,plain,(
% 2.97/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.97/0.98    inference(rectify,[],[f46])).
% 2.97/0.98  
% 2.97/0.98  fof(f48,plain,(
% 2.97/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f49,plain,(
% 2.97/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 2.97/0.98  
% 2.97/0.98  fof(f64,plain,(
% 2.97/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f11,axiom,(
% 2.97/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.97/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f30,plain,(
% 2.97/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.97/0.98    inference(ennf_transformation,[],[f11])).
% 2.97/0.98  
% 2.97/0.98  fof(f81,plain,(
% 2.97/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f30])).
% 2.97/0.98  
% 2.97/0.98  cnf(c_27,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.97/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.97/0.98      | ~ v1_funct_1(X0)
% 2.97/0.98      | ~ v1_funct_1(X3) ),
% 2.97/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1949,plain,
% 2.97/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.97/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.97/0.98      | v1_funct_1(X0) != iProver_top
% 2.97/0.98      | v1_funct_1(X3) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_23,plain,
% 2.97/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.97/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.98      | X3 = X2 ),
% 2.97/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_33,negated_conjecture,
% 2.97/0.98      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
% 2.97/0.98      inference(cnf_transformation,[],[f102]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_717,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | X3 = X0
% 2.97/0.98      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
% 2.97/0.98      | k6_partfun1(sK2) != X3
% 2.97/0.98      | sK2 != X2
% 2.97/0.98      | sK2 != X1 ),
% 2.97/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_718,plain,
% 2.97/0.98      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.97/0.98      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.97/0.98      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 2.97/0.98      inference(unflattening,[status(thm)],[c_717]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_24,plain,
% 2.97/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.97/0.98      inference(cnf_transformation,[],[f107]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_726,plain,
% 2.97/0.98      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.97/0.98      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 2.97/0.98      inference(forward_subsumption_resolution,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_718,c_24]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1927,plain,
% 2.97/0.98      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 2.97/0.98      | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5171,plain,
% 2.97/0.99      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2)
% 2.97/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.97/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.97/0.99      | v1_funct_1(sK4) != iProver_top
% 2.97/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1949,c_1927]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_39,negated_conjecture,
% 2.97/0.99      ( v1_funct_1(sK4) ),
% 2.97/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_40,plain,
% 2.97/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_37,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_42,plain,
% 2.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_36,negated_conjecture,
% 2.97/0.99      ( v1_funct_1(sK5) ),
% 2.97/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_43,plain,
% 2.97/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_34,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_45,plain,
% 2.97/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5810,plain,
% 2.97/0.99      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_5171,c_40,c_42,c_43,c_45]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_31,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.99      | ~ v1_funct_2(X3,X4,X1)
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_funct_1(X3)
% 2.97/0.99      | v2_funct_1(X3)
% 2.97/0.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.97/0.99      | k1_xboole_0 = X2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1946,plain,
% 2.97/0.99      ( k1_xboole_0 = X0
% 2.97/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.97/0.99      | v1_funct_2(X3,X4,X2) != iProver_top
% 2.97/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 2.97/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.97/0.99      | v1_funct_1(X1) != iProver_top
% 2.97/0.99      | v1_funct_1(X3) != iProver_top
% 2.97/0.99      | v2_funct_1(X3) = iProver_top
% 2.97/0.99      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5836,plain,
% 2.97/0.99      ( sK2 = k1_xboole_0
% 2.97/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 2.97/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 2.97/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.97/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.97/0.99      | v1_funct_1(sK4) != iProver_top
% 2.97/0.99      | v1_funct_1(sK5) != iProver_top
% 2.97/0.99      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 2.97/0.99      | v2_funct_1(sK4) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_5810,c_1946]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_38,negated_conjecture,
% 2.97/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_41,plain,
% 2.97/0.99      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_35,negated_conjecture,
% 2.97/0.99      ( v1_funct_2(sK5,sK3,sK2) ),
% 2.97/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_44,plain,
% 2.97/0.99      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_19,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_10,plain,
% 2.97/0.99      ( v5_relat_1(X0,X1)
% 2.97/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_25,plain,
% 2.97/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.97/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f111]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_32,negated_conjecture,
% 2.97/0.99      ( ~ v2_funct_2(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 2.97/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_413,plain,
% 2.97/0.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.97/0.99      | ~ v2_funct_1(sK4)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k2_relat_1(X0) != sK2
% 2.97/0.99      | sK5 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_414,plain,
% 2.97/0.99      ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
% 2.97/0.99      | ~ v2_funct_1(sK4)
% 2.97/0.99      | ~ v1_relat_1(sK5)
% 2.97/0.99      | k2_relat_1(sK5) != sK2 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_413]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_587,plain,
% 2.97/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.97/0.99      | ~ v2_funct_1(sK4)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | ~ v1_relat_1(sK5)
% 2.97/0.99      | k2_relat_1(sK5) != X1
% 2.97/0.99      | k2_relat_1(sK5) != sK2
% 2.97/0.99      | sK5 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_414]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_588,plain,
% 2.97/0.99      ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
% 2.97/0.99      | ~ v2_funct_1(sK4)
% 2.97/0.99      | ~ v1_relat_1(sK5)
% 2.97/0.99      | k2_relat_1(sK5) != sK2 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_587]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6,plain,
% 2.97/0.99      ( r1_tarski(X0,X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f108]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_598,plain,
% 2.97/0.99      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK5) | k2_relat_1(sK5) != sK2 ),
% 2.97/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_588,c_6]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_629,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ v2_funct_1(sK4)
% 2.97/0.99      | k2_relat_1(sK5) != sK2
% 2.97/0.99      | sK5 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_598]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_630,plain,
% 2.97/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.99      | ~ v2_funct_1(sK4)
% 2.97/0.99      | k2_relat_1(sK5) != sK2 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1272,plain,
% 2.97/0.99      ( ~ v2_funct_1(sK4) | sP3_iProver_split | k2_relat_1(sK5) != sK2 ),
% 2.97/0.99      inference(splitting,
% 2.97/0.99                [splitting(split),new_symbols(definition,[])],
% 2.97/0.99                [c_630]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1322,plain,
% 2.97/0.99      ( k2_relat_1(sK5) != sK2
% 2.97/0.99      | v2_funct_1(sK4) != iProver_top
% 2.97/0.99      | sP3_iProver_split = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1945,plain,
% 2.97/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1271,plain,
% 2.97/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.99      | ~ sP3_iProver_split ),
% 2.97/0.99      inference(splitting,
% 2.97/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.97/0.99                [c_630]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1935,plain,
% 2.97/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.97/0.99      | sP3_iProver_split != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2598,plain,
% 2.97/0.99      ( sP3_iProver_split != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1945,c_1935]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_21,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1951,plain,
% 2.97/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.97/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3837,plain,
% 2.97/0.99      ( k2_relset_1(sK3,sK2,sK5) = k2_relat_1(sK5) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1945,c_1951]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_29,plain,
% 2.97/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.97/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.97/0.99      | ~ v1_funct_2(X3,X1,X0)
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.97/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.99      | ~ v1_funct_1(X2)
% 2.97/0.99      | ~ v1_funct_1(X3)
% 2.97/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_730,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.99      | ~ v1_funct_2(X3,X2,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.97/0.99      | ~ v1_funct_1(X3)
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 2.97/0.99      | k2_relset_1(X2,X1,X3) = X1
% 2.97/0.99      | k6_partfun1(X1) != k6_partfun1(sK2)
% 2.97/0.99      | sK2 != X1 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_731,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,sK2)
% 2.97/0.99      | ~ v1_funct_2(X2,sK2,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 2.97/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 2.97/0.99      | ~ v1_funct_1(X2)
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | k1_partfun1(sK2,X1,X1,sK2,X2,X0) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 2.97/0.99      | k2_relset_1(X1,sK2,X0) = sK2
% 2.97/0.99      | k6_partfun1(sK2) != k6_partfun1(sK2) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_730]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_817,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,sK2)
% 2.97/0.99      | ~ v1_funct_2(X2,sK2,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 2.97/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 2.97/0.99      | ~ v1_funct_1(X0)
% 2.97/0.99      | ~ v1_funct_1(X2)
% 2.97/0.99      | k1_partfun1(sK2,X1,X1,sK2,X2,X0) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 2.97/0.99      | k2_relset_1(X1,sK2,X0) = sK2 ),
% 2.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_731]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1926,plain,
% 2.97/0.99      ( k1_partfun1(sK2,X0,X0,sK2,X1,X2) != k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 2.97/0.99      | k2_relset_1(X0,sK2,X2) = sK2
% 2.97/0.99      | v1_funct_2(X2,X0,sK2) != iProver_top
% 2.97/0.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 2.97/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 2.97/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.97/0.99      | v1_funct_1(X2) != iProver_top
% 2.97/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2369,plain,
% 2.97/0.99      ( k2_relset_1(sK3,sK2,sK5) = sK2
% 2.97/0.99      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 2.97/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 2.97/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.97/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.97/0.99      | v1_funct_1(sK4) != iProver_top
% 2.97/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.97/0.99      inference(equality_resolution,[status(thm)],[c_1926]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2556,plain,
% 2.97/0.99      ( k2_relset_1(sK3,sK2,sK5) = sK2 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2369,c_40,c_41,c_42,c_43,c_44,c_45]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3846,plain,
% 2.97/0.99      ( k2_relat_1(sK5) = sK2 ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_3837,c_2556]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6714,plain,
% 2.97/0.99      ( v2_funct_1(k6_partfun1(sK2)) != iProver_top | sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_5836,c_40,c_41,c_42,c_43,c_44,c_45,c_1322,c_2598,
% 2.97/0.99                 c_3846]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6715,plain,
% 2.97/0.99      ( sK2 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK2)) != iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_6714]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_16,plain,
% 2.97/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1953,plain,
% 2.97/0.99      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6720,plain,
% 2.97/0.99      ( sK2 = k1_xboole_0 ),
% 2.97/0.99      inference(forward_subsumption_resolution,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_6715,c_1953]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1959,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.97/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8,plain,
% 2.97/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1955,plain,
% 2.97/0.99      ( v1_xboole_0(X0) != iProver_top
% 2.97/0.99      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1942,plain,
% 2.97/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_9,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.99      | ~ r2_hidden(X2,X0)
% 2.97/0.99      | ~ v1_xboole_0(X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1954,plain,
% 2.97/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.97/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.97/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4843,plain,
% 2.97/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.97/0.99      | v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1942,c_1954]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4888,plain,
% 2.97/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.97/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1955,c_4843]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5020,plain,
% 2.97/0.99      ( r1_tarski(sK4,X0) = iProver_top
% 2.97/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1959,c_4888]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_17,plain,
% 2.97/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_11,plain,
% 2.97/0.99      ( ~ v5_relat_1(X0,X1)
% 2.97/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12,plain,
% 2.97/0.99      ( v5_relat_1(k1_xboole_0,X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_555,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | X2 != X1
% 2.97/0.99      | k1_xboole_0 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_556,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
% 2.97/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_555]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1021,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
% 2.97/0.99      | k6_partfun1(X1) != k1_xboole_0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_556]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1269,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~ sP2_iProver_split ),
% 2.97/0.99      inference(splitting,
% 2.97/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.97/0.99                [c_1021]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1932,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
% 2.97/0.99      | sP2_iProver_split != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_13,plain,
% 2.97/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2003,plain,
% 2.97/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 2.97/0.99      | sP2_iProver_split != iProver_top ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_1932,c_13]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_15,plain,
% 2.97/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1270,plain,
% 2.97/0.99      ( sP2_iProver_split | sP1_iProver_split ),
% 2.97/0.99      inference(splitting,
% 2.97/0.99                [splitting(split),new_symbols(definition,[])],
% 2.97/0.99                [c_1021]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1315,plain,
% 2.97/0.99      ( sP2_iProver_split = iProver_top
% 2.97/0.99      | sP1_iProver_split = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1268,plain,
% 2.97/0.99      ( k6_partfun1(X0) != k1_xboole_0 | ~ sP1_iProver_split ),
% 2.97/0.99      inference(splitting,
% 2.97/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.97/0.99                [c_1021]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1319,plain,
% 2.97/0.99      ( k6_partfun1(X0) != k1_xboole_0
% 2.97/0.99      | sP1_iProver_split != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1321,plain,
% 2.97/0.99      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 2.97/0.99      | sP1_iProver_split != iProver_top ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1319]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2951,plain,
% 2.97/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2003,c_15,c_1315,c_1321]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1957,plain,
% 2.97/0.99      ( X0 = X1
% 2.97/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.97/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4718,plain,
% 2.97/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2951,c_1957]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5601,plain,
% 2.97/0.99      ( sK4 = k1_xboole_0 | v1_xboole_0(sK2) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_5020,c_4718]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2455,plain,
% 2.97/0.99      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_15,c_1953]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2456,plain,
% 2.97/0.99      ( v2_funct_1(k1_xboole_0) ),
% 2.97/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2455]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2599,plain,
% 2.97/0.99      ( ~ sP3_iProver_split ),
% 2.97/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2598]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1287,plain,
% 2.97/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.97/0.99      theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2605,plain,
% 2.97/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1287]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2607,plain,
% 2.97/0.99      ( v2_funct_1(sK4)
% 2.97/0.99      | ~ v2_funct_1(k1_xboole_0)
% 2.97/0.99      | sK4 != k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2605]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6632,plain,
% 2.97/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_5601,c_1272,c_2456,c_2599,c_2607,c_3846]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6722,plain,
% 2.97/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_6720,c_6632]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_0,plain,
% 2.97/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1962,plain,
% 2.97/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.97/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_18,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1952,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.97/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3481,plain,
% 2.97/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2951,c_1952]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3552,plain,
% 2.97/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1962,c_3481]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(contradiction,plain,
% 2.97/0.99      ( $false ),
% 2.97/0.99      inference(minisat,[status(thm)],[c_6722,c_3552]) ).
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  ------                               Statistics
% 2.97/0.99  
% 2.97/0.99  ------ General
% 2.97/0.99  
% 2.97/0.99  abstr_ref_over_cycles:                  0
% 2.97/0.99  abstr_ref_under_cycles:                 0
% 2.97/0.99  gc_basic_clause_elim:                   0
% 2.97/0.99  forced_gc_time:                         0
% 2.97/0.99  parsing_time:                           0.009
% 2.97/0.99  unif_index_cands_time:                  0.
% 2.97/0.99  unif_index_add_time:                    0.
% 2.97/0.99  orderings_time:                         0.
% 2.97/0.99  out_proof_time:                         0.01
% 2.97/0.99  total_time:                             0.236
% 2.97/0.99  num_of_symbols:                         61
% 2.97/0.99  num_of_terms:                           8984
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing
% 2.97/0.99  
% 2.97/0.99  num_of_splits:                          6
% 2.97/0.99  num_of_split_atoms:                     5
% 2.97/0.99  num_of_reused_defs:                     1
% 2.97/0.99  num_eq_ax_congr_red:                    29
% 2.97/0.99  num_of_sem_filtered_clauses:            4
% 2.97/0.99  num_of_subtypes:                        0
% 2.97/0.99  monotx_restored_types:                  0
% 2.97/0.99  sat_num_of_epr_types:                   0
% 2.97/0.99  sat_num_of_non_cyclic_types:            0
% 2.97/0.99  sat_guarded_non_collapsed_types:        0
% 2.97/0.99  num_pure_diseq_elim:                    0
% 2.97/0.99  simp_replaced_by:                       0
% 2.97/0.99  res_preprocessed:                       214
% 2.97/0.99  prep_upred:                             0
% 2.97/0.99  prep_unflattend:                        29
% 2.97/0.99  smt_new_axioms:                         0
% 2.97/0.99  pred_elim_cands:                        7
% 2.97/0.99  pred_elim:                              4
% 2.97/0.99  pred_elim_cl:                           5
% 2.97/0.99  pred_elim_cycles:                       9
% 2.97/0.99  merged_defs:                            0
% 2.97/0.99  merged_defs_ncl:                        0
% 2.97/0.99  bin_hyper_res:                          0
% 2.97/0.99  prep_cycles:                            5
% 2.97/0.99  pred_elim_time:                         0.01
% 2.97/0.99  splitting_time:                         0.
% 2.97/0.99  sem_filter_time:                        0.
% 2.97/0.99  monotx_time:                            0.
% 2.97/0.99  subtype_inf_time:                       0.
% 2.97/0.99  
% 2.97/0.99  ------ Problem properties
% 2.97/0.99  
% 2.97/0.99  clauses:                                40
% 2.97/0.99  conjectures:                            6
% 2.97/0.99  epr:                                    11
% 2.97/0.99  horn:                                   35
% 2.97/0.99  ground:                                 14
% 2.97/0.99  unary:                                  12
% 2.97/0.99  binary:                                 17
% 2.97/0.99  lits:                                   104
% 2.97/0.99  lits_eq:                                15
% 2.97/0.99  fd_pure:                                0
% 2.97/0.99  fd_pseudo:                              0
% 2.97/0.99  fd_cond:                                1
% 2.97/0.99  fd_pseudo_cond:                         1
% 2.97/0.99  ac_symbols:                             0
% 2.97/0.99  
% 2.97/0.99  ------ Propositional Solver
% 2.97/0.99  
% 2.97/0.99  prop_solver_calls:                      31
% 2.97/0.99  prop_fast_solver_calls:                 1437
% 2.97/0.99  smt_solver_calls:                       0
% 2.97/0.99  smt_fast_solver_calls:                  0
% 2.97/0.99  prop_num_of_clauses:                    2533
% 2.97/0.99  prop_preprocess_simplified:             8802
% 2.97/0.99  prop_fo_subsumed:                       34
% 2.97/0.99  prop_solver_time:                       0.
% 2.97/0.99  smt_solver_time:                        0.
% 2.97/0.99  smt_fast_solver_time:                   0.
% 2.97/0.99  prop_fast_solver_time:                  0.
% 2.97/0.99  prop_unsat_core_time:                   0.
% 2.97/0.99  
% 2.97/0.99  ------ QBF
% 2.97/0.99  
% 2.97/0.99  qbf_q_res:                              0
% 2.97/0.99  qbf_num_tautologies:                    0
% 2.97/0.99  qbf_prep_cycles:                        0
% 2.97/0.99  
% 2.97/0.99  ------ BMC1
% 2.97/0.99  
% 2.97/0.99  bmc1_current_bound:                     -1
% 2.97/0.99  bmc1_last_solved_bound:                 -1
% 2.97/0.99  bmc1_unsat_core_size:                   -1
% 2.97/0.99  bmc1_unsat_core_parents_size:           -1
% 2.97/0.99  bmc1_merge_next_fun:                    0
% 2.97/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation
% 2.97/0.99  
% 2.97/0.99  inst_num_of_clauses:                    730
% 2.97/0.99  inst_num_in_passive:                    85
% 2.97/0.99  inst_num_in_active:                     341
% 2.97/0.99  inst_num_in_unprocessed:                308
% 2.97/0.99  inst_num_of_loops:                      400
% 2.97/0.99  inst_num_of_learning_restarts:          0
% 2.97/0.99  inst_num_moves_active_passive:          57
% 2.97/0.99  inst_lit_activity:                      0
% 2.97/0.99  inst_lit_activity_moves:                0
% 2.97/0.99  inst_num_tautologies:                   0
% 2.97/0.99  inst_num_prop_implied:                  0
% 2.97/0.99  inst_num_existing_simplified:           0
% 2.97/0.99  inst_num_eq_res_simplified:             0
% 2.97/0.99  inst_num_child_elim:                    0
% 2.97/0.99  inst_num_of_dismatching_blockings:      117
% 2.97/0.99  inst_num_of_non_proper_insts:           487
% 2.97/0.99  inst_num_of_duplicates:                 0
% 2.97/0.99  inst_inst_num_from_inst_to_res:         0
% 2.97/0.99  inst_dismatching_checking_time:         0.
% 2.97/0.99  
% 2.97/0.99  ------ Resolution
% 2.97/0.99  
% 2.97/0.99  res_num_of_clauses:                     0
% 2.97/0.99  res_num_in_passive:                     0
% 2.97/0.99  res_num_in_active:                      0
% 2.97/0.99  res_num_of_loops:                       219
% 2.97/0.99  res_forward_subset_subsumed:            75
% 2.97/0.99  res_backward_subset_subsumed:           12
% 2.97/0.99  res_forward_subsumed:                   0
% 2.97/0.99  res_backward_subsumed:                  1
% 2.97/0.99  res_forward_subsumption_resolution:     4
% 2.97/0.99  res_backward_subsumption_resolution:    0
% 2.97/0.99  res_clause_to_clause_subsumption:       302
% 2.97/0.99  res_orphan_elimination:                 0
% 2.97/0.99  res_tautology_del:                      21
% 2.97/0.99  res_num_eq_res_simplified:              1
% 2.97/0.99  res_num_sel_changes:                    0
% 2.97/0.99  res_moves_from_active_to_pass:          0
% 2.97/0.99  
% 2.97/0.99  ------ Superposition
% 2.97/0.99  
% 2.97/0.99  sup_time_total:                         0.
% 2.97/0.99  sup_time_generating:                    0.
% 2.97/0.99  sup_time_sim_full:                      0.
% 2.97/0.99  sup_time_sim_immed:                     0.
% 2.97/0.99  
% 2.97/0.99  sup_num_of_clauses:                     79
% 2.97/0.99  sup_num_in_active:                      60
% 2.97/0.99  sup_num_in_passive:                     19
% 2.97/0.99  sup_num_of_loops:                       79
% 2.97/0.99  sup_fw_superposition:                   58
% 2.97/0.99  sup_bw_superposition:                   30
% 2.97/0.99  sup_immediate_simplified:               17
% 2.97/0.99  sup_given_eliminated:                   0
% 2.97/0.99  comparisons_done:                       0
% 2.97/0.99  comparisons_avoided:                    0
% 2.97/0.99  
% 2.97/0.99  ------ Simplifications
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  sim_fw_subset_subsumed:                 7
% 2.97/0.99  sim_bw_subset_subsumed:                 1
% 2.97/0.99  sim_fw_subsumed:                        5
% 2.97/0.99  sim_bw_subsumed:                        3
% 2.97/0.99  sim_fw_subsumption_res:                 1
% 2.97/0.99  sim_bw_subsumption_res:                 0
% 2.97/0.99  sim_tautology_del:                      2
% 2.97/0.99  sim_eq_tautology_del:                   7
% 2.97/0.99  sim_eq_res_simp:                        1
% 2.97/0.99  sim_fw_demodulated:                     0
% 2.97/0.99  sim_bw_demodulated:                     19
% 2.97/0.99  sim_light_normalised:                   12
% 2.97/0.99  sim_joinable_taut:                      0
% 2.97/0.99  sim_joinable_simp:                      0
% 2.97/0.99  sim_ac_normalised:                      0
% 2.97/0.99  sim_smt_subsumption:                    0
% 2.97/0.99  
%------------------------------------------------------------------------------

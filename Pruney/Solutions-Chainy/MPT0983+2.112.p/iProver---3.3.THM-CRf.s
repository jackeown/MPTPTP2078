%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:09 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :  243 (1268 expanded)
%              Number of clauses        :  142 ( 362 expanded)
%              Number of leaves         :   31 ( 323 expanded)
%              Depth                    :   17
%              Number of atoms          :  743 (7779 expanded)
%              Number of equality atoms :  193 ( 522 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f22,axiom,(
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
    inference(ennf_transformation,[],[f22])).

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

fof(f95,plain,(
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

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

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
    inference(ennf_transformation,[],[f24])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f46,f61,f60])).

fof(f103,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f62])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f88,f94])).

fof(f97,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f107,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f84,f94])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f82,f94])).

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

fof(f51,plain,(
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

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f113,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f90])).

fof(f104,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f101,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_48186,plain,
    ( ~ r2_hidden(sK1(X0,sK4),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_48188,plain,
    ( ~ r2_hidden(sK1(sK2,sK4),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_48186])).

cnf(c_767,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_18584,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_18586,plain,
    ( v2_funct_1(sK4)
    | ~ v2_funct_1(sK2)
    | sK4 != sK2 ),
    inference(instantiation,[status(thm)],[c_18584])).

cnf(c_759,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_13539,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_13541,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_13539])).

cnf(c_11101,plain,
    ( ~ r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0))
    | ~ v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11103,plain,
    ( ~ r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2))
    | ~ v1_xboole_0(k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_11101])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_756,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_755,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4805,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_756,c_755])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
    | k6_partfun1(sK2) != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_448,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_25,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_71,plain,
    ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_450,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_71])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2065,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_2838,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(c_4350,plain,
    ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_6783,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_40,c_38,c_37,c_35,c_71,c_448,c_4350])).

cnf(c_7889,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
    inference(resolution,[status(thm)],[c_4805,c_6783])).

cnf(c_8568,plain,
    ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
    | ~ v2_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[status(thm)],[c_7889,c_767])).

cnf(c_20,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_86,plain,
    ( v2_funct_1(k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_8974,plain,
    ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8568,c_86])).

cnf(c_9097,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | v2_funct_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_32,c_8974])).

cnf(c_6819,plain,
    ( ~ r1_tarski(X0,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
    | r1_tarski(X1,k6_partfun1(sK2))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_6783,c_759])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8882,plain,
    ( r1_tarski(X0,k6_partfun1(sK2))
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6819,c_8])).

cnf(c_8884,plain,
    ( r1_tarski(sK2,k6_partfun1(sK2))
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8882])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1400,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1393,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1399,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3582,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1399])).

cnf(c_5935,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_3582])).

cnf(c_5936,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5935])).

cnf(c_5938,plain,
    ( v1_xboole_0(k6_partfun1(sK2))
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5936])).

cnf(c_1384,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1387,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1390,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4674,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1390])).

cnf(c_44,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4995,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4674,c_44])).

cnf(c_4996,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4995])).

cnf(c_5007,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_4996])).

cnf(c_1776,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2045,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_2728,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_4336,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2728])).

cnf(c_5240,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5007,c_40,c_38,c_37,c_35,c_4336])).

cnf(c_1380,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_5243,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
    | m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5240,c_1380])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5245,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5240,c_1392])).

cnf(c_5664,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5243,c_41,c_43,c_44,c_46,c_5245])).

cnf(c_5667,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
    inference(demodulation,[status(thm)],[c_5664,c_5240])).

cnf(c_1388,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5674,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k6_partfun1(sK2)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5667,c_1388])).

cnf(c_17,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1396,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5668,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5664,c_1396])).

cnf(c_18,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5669,plain,
    ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5668,c_18])).

cnf(c_5608,plain,
    ( ~ r2_hidden(sK1(sK4,X0),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5610,plain,
    ( ~ r2_hidden(sK1(sK4,sK2),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5608])).

cnf(c_3584,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1399])).

cnf(c_3928,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_3584])).

cnf(c_3929,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3928])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3417,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3419,plain,
    ( r1_tarski(sK2,sK4)
    | r2_hidden(sK1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_3417])).

cnf(c_3329,plain,
    ( r1_tarski(k6_partfun1(X0),X1)
    | r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3331,plain,
    ( r1_tarski(k6_partfun1(sK2),sK2)
    | r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3329])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_15])).

cnf(c_1379,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_2801,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1379])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2088,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK2))
    | v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_13,c_35])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2095,plain,
    ( v1_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2088,c_16])).

cnf(c_2096,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_3067,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_2096])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1403,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3072,plain,
    ( k2_relat_1(sK5) = sK2
    | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3067,c_1403])).

cnf(c_2478,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2480,plain,
    ( ~ r1_tarski(sK4,sK2)
    | ~ r1_tarski(sK2,sK4)
    | sK4 = sK2 ),
    inference(instantiation,[status(thm)],[c_2478])).

cnf(c_2458,plain,
    ( r1_tarski(sK4,X0)
    | r2_hidden(sK1(sK4,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2460,plain,
    ( r1_tarski(sK4,sK2)
    | r2_hidden(sK1(sK4,sK2),sK4) ),
    inference(instantiation,[status(thm)],[c_2458])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_33,negated_conjecture,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_466,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_467,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_520,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_467])).

cnf(c_521,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_531,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_521,c_6])).

cnf(c_2371,plain,
    ( ~ v2_funct_1(sK4)
    | k2_relat_1(sK5) != sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2095,c_531])).

cnf(c_2090,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_13,c_38])).

cnf(c_2102,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2090,c_16])).

cnf(c_2103,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2102])).

cnf(c_1892,plain,
    ( ~ r1_tarski(X0,k6_partfun1(X1))
    | ~ r1_tarski(k6_partfun1(X1),X0)
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1894,plain,
    ( ~ r1_tarski(k6_partfun1(sK2),sK2)
    | ~ r1_tarski(sK2,k6_partfun1(sK2))
    | sK2 = k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_1679,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1681,plain,
    ( ~ v2_funct_1(k6_partfun1(sK2))
    | v2_funct_1(sK2)
    | sK2 != k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_532,plain,
    ( k2_relat_1(sK5) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_430,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_431,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_433,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_121,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_117,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_87,plain,
    ( v2_funct_1(k6_partfun1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_45,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_42,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48188,c_18586,c_13541,c_11103,c_9097,c_8884,c_5938,c_5674,c_5669,c_5610,c_3929,c_3419,c_3331,c_3072,c_2480,c_2460,c_2371,c_2103,c_2096,c_1894,c_1681,c_532,c_433,c_121,c_117,c_87,c_86,c_46,c_35,c_45,c_36,c_44,c_37,c_43,c_38,c_42,c_39,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:57:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 12.00/1.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.00/1.97  
% 12.00/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.00/1.97  
% 12.00/1.97  ------  iProver source info
% 12.00/1.97  
% 12.00/1.97  git: date: 2020-06-30 10:37:57 +0100
% 12.00/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.00/1.97  git: non_committed_changes: false
% 12.00/1.97  git: last_make_outside_of_git: false
% 12.00/1.97  
% 12.00/1.97  ------ 
% 12.00/1.97  ------ Parsing...
% 12.00/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.00/1.97  
% 12.00/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 12.00/1.97  
% 12.00/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.00/1.97  
% 12.00/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.00/1.97  ------ Proving...
% 12.00/1.97  ------ Problem Properties 
% 12.00/1.97  
% 12.00/1.97  
% 12.00/1.97  clauses                                 33
% 12.00/1.97  conjectures                             6
% 12.00/1.97  EPR                                     10
% 12.00/1.97  Horn                                    30
% 12.00/1.97  unary                                   14
% 12.00/1.97  binary                                  7
% 12.00/1.97  lits                                    81
% 12.00/1.97  lits eq                                 7
% 12.00/1.97  fd_pure                                 0
% 12.00/1.97  fd_pseudo                               0
% 12.00/1.97  fd_cond                                 1
% 12.00/1.97  fd_pseudo_cond                          1
% 12.00/1.97  AC symbols                              0
% 12.00/1.97  
% 12.00/1.97  ------ Input Options Time Limit: Unbounded
% 12.00/1.97  
% 12.00/1.97  
% 12.00/1.97  ------ 
% 12.00/1.97  Current options:
% 12.00/1.97  ------ 
% 12.00/1.97  
% 12.00/1.97  
% 12.00/1.97  
% 12.00/1.97  
% 12.00/1.97  ------ Proving...
% 12.00/1.97  
% 12.00/1.97  
% 12.00/1.97  % SZS status Theorem for theBenchmark.p
% 12.00/1.97  
% 12.00/1.97  % SZS output start CNFRefutation for theBenchmark.p
% 12.00/1.97  
% 12.00/1.97  fof(f1,axiom,(
% 12.00/1.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f47,plain,(
% 12.00/1.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 12.00/1.97    inference(nnf_transformation,[],[f1])).
% 12.00/1.97  
% 12.00/1.97  fof(f48,plain,(
% 12.00/1.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 12.00/1.97    inference(rectify,[],[f47])).
% 12.00/1.97  
% 12.00/1.97  fof(f49,plain,(
% 12.00/1.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 12.00/1.97    introduced(choice_axiom,[])).
% 12.00/1.97  
% 12.00/1.97  fof(f50,plain,(
% 12.00/1.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 12.00/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 12.00/1.97  
% 12.00/1.97  fof(f63,plain,(
% 12.00/1.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f50])).
% 12.00/1.97  
% 12.00/1.97  fof(f22,axiom,(
% 12.00/1.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f43,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 12.00/1.97    inference(ennf_transformation,[],[f22])).
% 12.00/1.97  
% 12.00/1.97  fof(f44,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 12.00/1.97    inference(flattening,[],[f43])).
% 12.00/1.97  
% 12.00/1.97  fof(f95,plain,(
% 12.00/1.97    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f44])).
% 12.00/1.97  
% 12.00/1.97  fof(f16,axiom,(
% 12.00/1.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f35,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 12.00/1.97    inference(ennf_transformation,[],[f16])).
% 12.00/1.97  
% 12.00/1.97  fof(f36,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.00/1.97    inference(flattening,[],[f35])).
% 12.00/1.97  
% 12.00/1.97  fof(f58,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.00/1.97    inference(nnf_transformation,[],[f36])).
% 12.00/1.97  
% 12.00/1.97  fof(f86,plain,(
% 12.00/1.97    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.00/1.97    inference(cnf_transformation,[],[f58])).
% 12.00/1.97  
% 12.00/1.97  fof(f23,conjecture,(
% 12.00/1.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f24,negated_conjecture,(
% 12.00/1.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 12.00/1.97    inference(negated_conjecture,[],[f23])).
% 12.00/1.97  
% 12.00/1.97  fof(f45,plain,(
% 12.00/1.97    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 12.00/1.97    inference(ennf_transformation,[],[f24])).
% 12.00/1.97  
% 12.00/1.97  fof(f46,plain,(
% 12.00/1.97    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 12.00/1.97    inference(flattening,[],[f45])).
% 12.00/1.97  
% 12.00/1.97  fof(f61,plain,(
% 12.00/1.97    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 12.00/1.97    introduced(choice_axiom,[])).
% 12.00/1.97  
% 12.00/1.97  fof(f60,plain,(
% 12.00/1.97    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 12.00/1.97    introduced(choice_axiom,[])).
% 12.00/1.97  
% 12.00/1.97  fof(f62,plain,(
% 12.00/1.97    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 12.00/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f46,f61,f60])).
% 12.00/1.97  
% 12.00/1.97  fof(f103,plain,(
% 12.00/1.97    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  fof(f17,axiom,(
% 12.00/1.97    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f88,plain,(
% 12.00/1.97    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 12.00/1.97    inference(cnf_transformation,[],[f17])).
% 12.00/1.97  
% 12.00/1.97  fof(f21,axiom,(
% 12.00/1.97    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f94,plain,(
% 12.00/1.97    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f21])).
% 12.00/1.97  
% 12.00/1.97  fof(f109,plain,(
% 12.00/1.97    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 12.00/1.97    inference(definition_unfolding,[],[f88,f94])).
% 12.00/1.97  
% 12.00/1.97  fof(f97,plain,(
% 12.00/1.97    v1_funct_1(sK4)),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  fof(f99,plain,(
% 12.00/1.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  fof(f100,plain,(
% 12.00/1.97    v1_funct_1(sK5)),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  fof(f102,plain,(
% 12.00/1.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  fof(f19,axiom,(
% 12.00/1.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f39,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 12.00/1.97    inference(ennf_transformation,[],[f19])).
% 12.00/1.97  
% 12.00/1.97  fof(f40,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 12.00/1.97    inference(flattening,[],[f39])).
% 12.00/1.97  
% 12.00/1.97  fof(f92,plain,(
% 12.00/1.97    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f40])).
% 12.00/1.97  
% 12.00/1.97  fof(f14,axiom,(
% 12.00/1.97    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f84,plain,(
% 12.00/1.97    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 12.00/1.97    inference(cnf_transformation,[],[f14])).
% 12.00/1.97  
% 12.00/1.97  fof(f107,plain,(
% 12.00/1.97    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 12.00/1.97    inference(definition_unfolding,[],[f84,f94])).
% 12.00/1.97  
% 12.00/1.97  fof(f4,axiom,(
% 12.00/1.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f71,plain,(
% 12.00/1.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f4])).
% 12.00/1.97  
% 12.00/1.97  fof(f7,axiom,(
% 12.00/1.97    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f29,plain,(
% 12.00/1.97    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 12.00/1.97    inference(ennf_transformation,[],[f7])).
% 12.00/1.97  
% 12.00/1.97  fof(f74,plain,(
% 12.00/1.97    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f29])).
% 12.00/1.97  
% 12.00/1.97  fof(f8,axiom,(
% 12.00/1.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f30,plain,(
% 12.00/1.97    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 12.00/1.97    inference(ennf_transformation,[],[f8])).
% 12.00/1.97  
% 12.00/1.97  fof(f75,plain,(
% 12.00/1.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f30])).
% 12.00/1.97  
% 12.00/1.97  fof(f20,axiom,(
% 12.00/1.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f41,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 12.00/1.97    inference(ennf_transformation,[],[f20])).
% 12.00/1.97  
% 12.00/1.97  fof(f42,plain,(
% 12.00/1.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 12.00/1.97    inference(flattening,[],[f41])).
% 12.00/1.97  
% 12.00/1.97  fof(f93,plain,(
% 12.00/1.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f42])).
% 12.00/1.97  
% 12.00/1.97  fof(f12,axiom,(
% 12.00/1.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f33,plain,(
% 12.00/1.97    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 12.00/1.97    inference(ennf_transformation,[],[f12])).
% 12.00/1.97  
% 12.00/1.97  fof(f80,plain,(
% 12.00/1.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f33])).
% 12.00/1.97  
% 12.00/1.97  fof(f13,axiom,(
% 12.00/1.97    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f82,plain,(
% 12.00/1.97    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 12.00/1.97    inference(cnf_transformation,[],[f13])).
% 12.00/1.97  
% 12.00/1.97  fof(f105,plain,(
% 12.00/1.97    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 12.00/1.97    inference(definition_unfolding,[],[f82,f94])).
% 12.00/1.97  
% 12.00/1.97  fof(f2,axiom,(
% 12.00/1.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f26,plain,(
% 12.00/1.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.00/1.97    inference(ennf_transformation,[],[f2])).
% 12.00/1.97  
% 12.00/1.97  fof(f51,plain,(
% 12.00/1.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/1.97    inference(nnf_transformation,[],[f26])).
% 12.00/1.97  
% 12.00/1.97  fof(f52,plain,(
% 12.00/1.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/1.97    inference(rectify,[],[f51])).
% 12.00/1.97  
% 12.00/1.97  fof(f53,plain,(
% 12.00/1.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 12.00/1.97    introduced(choice_axiom,[])).
% 12.00/1.97  
% 12.00/1.97  fof(f54,plain,(
% 12.00/1.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 12.00/1.97  
% 12.00/1.97  fof(f66,plain,(
% 12.00/1.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f54])).
% 12.00/1.97  
% 12.00/1.97  fof(f15,axiom,(
% 12.00/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f25,plain,(
% 12.00/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 12.00/1.97    inference(pure_predicate_removal,[],[f15])).
% 12.00/1.97  
% 12.00/1.97  fof(f34,plain,(
% 12.00/1.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.00/1.97    inference(ennf_transformation,[],[f25])).
% 12.00/1.97  
% 12.00/1.97  fof(f85,plain,(
% 12.00/1.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.00/1.97    inference(cnf_transformation,[],[f34])).
% 12.00/1.97  
% 12.00/1.97  fof(f10,axiom,(
% 12.00/1.97    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f32,plain,(
% 12.00/1.97    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 12.00/1.97    inference(ennf_transformation,[],[f10])).
% 12.00/1.97  
% 12.00/1.97  fof(f57,plain,(
% 12.00/1.97    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 12.00/1.97    inference(nnf_transformation,[],[f32])).
% 12.00/1.97  
% 12.00/1.97  fof(f77,plain,(
% 12.00/1.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f57])).
% 12.00/1.97  
% 12.00/1.97  fof(f9,axiom,(
% 12.00/1.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f31,plain,(
% 12.00/1.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 12.00/1.97    inference(ennf_transformation,[],[f9])).
% 12.00/1.97  
% 12.00/1.97  fof(f76,plain,(
% 12.00/1.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f31])).
% 12.00/1.97  
% 12.00/1.97  fof(f11,axiom,(
% 12.00/1.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f79,plain,(
% 12.00/1.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 12.00/1.97    inference(cnf_transformation,[],[f11])).
% 12.00/1.97  
% 12.00/1.97  fof(f3,axiom,(
% 12.00/1.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f55,plain,(
% 12.00/1.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.00/1.97    inference(nnf_transformation,[],[f3])).
% 12.00/1.97  
% 12.00/1.97  fof(f56,plain,(
% 12.00/1.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.00/1.97    inference(flattening,[],[f55])).
% 12.00/1.97  
% 12.00/1.97  fof(f70,plain,(
% 12.00/1.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f56])).
% 12.00/1.97  
% 12.00/1.97  fof(f78,plain,(
% 12.00/1.97    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f57])).
% 12.00/1.97  
% 12.00/1.97  fof(f18,axiom,(
% 12.00/1.97    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f37,plain,(
% 12.00/1.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 12.00/1.97    inference(ennf_transformation,[],[f18])).
% 12.00/1.97  
% 12.00/1.97  fof(f38,plain,(
% 12.00/1.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 12.00/1.97    inference(flattening,[],[f37])).
% 12.00/1.97  
% 12.00/1.97  fof(f59,plain,(
% 12.00/1.97    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 12.00/1.97    inference(nnf_transformation,[],[f38])).
% 12.00/1.97  
% 12.00/1.97  fof(f90,plain,(
% 12.00/1.97    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f59])).
% 12.00/1.97  
% 12.00/1.97  fof(f113,plain,(
% 12.00/1.97    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 12.00/1.97    inference(equality_resolution,[],[f90])).
% 12.00/1.97  
% 12.00/1.97  fof(f104,plain,(
% 12.00/1.97    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  fof(f69,plain,(
% 12.00/1.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 12.00/1.97    inference(cnf_transformation,[],[f56])).
% 12.00/1.97  
% 12.00/1.97  fof(f110,plain,(
% 12.00/1.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.00/1.97    inference(equality_resolution,[],[f69])).
% 12.00/1.97  
% 12.00/1.97  fof(f5,axiom,(
% 12.00/1.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f72,plain,(
% 12.00/1.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f5])).
% 12.00/1.97  
% 12.00/1.97  fof(f6,axiom,(
% 12.00/1.97    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 12.00/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/1.97  
% 12.00/1.97  fof(f27,plain,(
% 12.00/1.97    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 12.00/1.97    inference(ennf_transformation,[],[f6])).
% 12.00/1.97  
% 12.00/1.97  fof(f28,plain,(
% 12.00/1.97    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 12.00/1.97    inference(flattening,[],[f27])).
% 12.00/1.97  
% 12.00/1.97  fof(f73,plain,(
% 12.00/1.97    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 12.00/1.97    inference(cnf_transformation,[],[f28])).
% 12.00/1.97  
% 12.00/1.97  fof(f68,plain,(
% 12.00/1.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 12.00/1.97    inference(cnf_transformation,[],[f56])).
% 12.00/1.97  
% 12.00/1.97  fof(f111,plain,(
% 12.00/1.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.00/1.97    inference(equality_resolution,[],[f68])).
% 12.00/1.97  
% 12.00/1.97  fof(f101,plain,(
% 12.00/1.97    v1_funct_2(sK5,sK3,sK2)),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  fof(f98,plain,(
% 12.00/1.97    v1_funct_2(sK4,sK2,sK3)),
% 12.00/1.97    inference(cnf_transformation,[],[f62])).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1,plain,
% 12.00/1.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 12.00/1.97      inference(cnf_transformation,[],[f63]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_48186,plain,
% 12.00/1.97      ( ~ r2_hidden(sK1(X0,sK4),X0) | ~ v1_xboole_0(X0) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_1]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_48188,plain,
% 12.00/1.97      ( ~ r2_hidden(sK1(sK2,sK4),sK2) | ~ v1_xboole_0(sK2) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_48186]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_767,plain,
% 12.00/1.97      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 12.00/1.97      theory(equality) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_18584,plain,
% 12.00/1.97      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_767]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_18586,plain,
% 12.00/1.97      ( v2_funct_1(sK4) | ~ v2_funct_1(sK2) | sK4 != sK2 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_18584]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_759,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.00/1.97      theory(equality) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_13539,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,X1)
% 12.00/1.97      | r1_tarski(X2,k1_xboole_0)
% 12.00/1.97      | X2 != X0
% 12.00/1.97      | k1_xboole_0 != X1 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_759]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_13541,plain,
% 12.00/1.97      ( ~ r1_tarski(sK2,sK2)
% 12.00/1.97      | r1_tarski(sK2,k1_xboole_0)
% 12.00/1.97      | sK2 != sK2
% 12.00/1.97      | k1_xboole_0 != sK2 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_13539]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_11101,plain,
% 12.00/1.97      ( ~ r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0))
% 12.00/1.97      | ~ v1_xboole_0(k6_partfun1(X0)) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_1]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_11103,plain,
% 12.00/1.97      ( ~ r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2))
% 12.00/1.97      | ~ v1_xboole_0(k6_partfun1(sK2)) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_11101]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_32,plain,
% 12.00/1.97      ( ~ v1_funct_2(X0,X1,X2)
% 12.00/1.97      | ~ v1_funct_2(X3,X4,X1)
% 12.00/1.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 12.00/1.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | ~ v1_funct_1(X0)
% 12.00/1.97      | ~ v1_funct_1(X3)
% 12.00/1.97      | v2_funct_1(X3)
% 12.00/1.97      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 12.00/1.97      | k1_xboole_0 = X2 ),
% 12.00/1.97      inference(cnf_transformation,[],[f95]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_756,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_755,plain,( X0 = X0 ),theory(equality) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_4805,plain,
% 12.00/1.97      ( X0 != X1 | X1 = X0 ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_756,c_755]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_24,plain,
% 12.00/1.97      ( ~ r2_relset_1(X0,X1,X2,X3)
% 12.00/1.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.00/1.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.00/1.97      | X3 = X2 ),
% 12.00/1.97      inference(cnf_transformation,[],[f86]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_34,negated_conjecture,
% 12.00/1.97      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
% 12.00/1.97      inference(cnf_transformation,[],[f103]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_447,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | X3 = X0
% 12.00/1.97      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
% 12.00/1.97      | k6_partfun1(sK2) != X3
% 12.00/1.97      | sK2 != X2
% 12.00/1.97      | sK2 != X1 ),
% 12.00/1.97      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_448,plain,
% 12.00/1.97      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 12.00/1.97      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 12.00/1.97      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 12.00/1.97      inference(unflattening,[status(thm)],[c_447]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_25,plain,
% 12.00/1.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 12.00/1.97      inference(cnf_transformation,[],[f109]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_71,plain,
% 12.00/1.97      ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_25]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_450,plain,
% 12.00/1.97      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 12.00/1.97      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 12.00/1.97      inference(global_propositional_subsumption,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_448,c_71]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_40,negated_conjecture,
% 12.00/1.97      ( v1_funct_1(sK4) ),
% 12.00/1.97      inference(cnf_transformation,[],[f97]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_38,negated_conjecture,
% 12.00/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 12.00/1.97      inference(cnf_transformation,[],[f99]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_37,negated_conjecture,
% 12.00/1.97      ( v1_funct_1(sK5) ),
% 12.00/1.97      inference(cnf_transformation,[],[f100]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_35,negated_conjecture,
% 12.00/1.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 12.00/1.97      inference(cnf_transformation,[],[f102]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_28,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 12.00/1.97      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 12.00/1.97      | ~ v1_funct_1(X0)
% 12.00/1.97      | ~ v1_funct_1(X3) ),
% 12.00/1.97      inference(cnf_transformation,[],[f92]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1766,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 12.00/1.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 12.00/1.97      | ~ v1_funct_1(X0)
% 12.00/1.97      | ~ v1_funct_1(sK4) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_28]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2065,plain,
% 12.00/1.97      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 12.00/1.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.00/1.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | ~ v1_funct_1(sK5) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_1766]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2838,plain,
% 12.00/1.97      ( m1_subset_1(k1_partfun1(X0,X1,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 12.00/1.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.00/1.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | ~ v1_funct_1(sK5) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_2065]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_4350,plain,
% 12.00/1.97      ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 12.00/1.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 12.00/1.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | ~ v1_funct_1(sK5) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_2838]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_6783,plain,
% 12.00/1.97      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 12.00/1.97      inference(global_propositional_subsumption,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_450,c_40,c_38,c_37,c_35,c_71,c_448,c_4350]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_7889,plain,
% 12.00/1.97      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_4805,c_6783]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_8568,plain,
% 12.00/1.97      ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
% 12.00/1.97      | ~ v2_funct_1(k6_partfun1(sK2)) ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_7889,c_767]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_20,plain,
% 12.00/1.97      ( v2_funct_1(k6_partfun1(X0)) ),
% 12.00/1.97      inference(cnf_transformation,[],[f107]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_86,plain,
% 12.00/1.97      ( v2_funct_1(k6_partfun1(sK2)) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_20]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_8974,plain,
% 12.00/1.97      ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)) ),
% 12.00/1.97      inference(global_propositional_subsumption,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_8568,c_86]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_9097,plain,
% 12.00/1.97      ( ~ v1_funct_2(sK4,sK2,sK3)
% 12.00/1.97      | ~ v1_funct_2(sK5,sK3,sK2)
% 12.00/1.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 12.00/1.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | ~ v1_funct_1(sK5)
% 12.00/1.97      | v2_funct_1(sK4)
% 12.00/1.97      | k1_xboole_0 = sK2 ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_32,c_8974]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_6819,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
% 12.00/1.97      | r1_tarski(X1,k6_partfun1(sK2))
% 12.00/1.97      | X1 != X0 ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_6783,c_759]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_8,plain,
% 12.00/1.97      ( r1_tarski(k1_xboole_0,X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f71]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_8882,plain,
% 12.00/1.97      ( r1_tarski(X0,k6_partfun1(sK2)) | X0 != k1_xboole_0 ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_6819,c_8]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_8884,plain,
% 12.00/1.97      ( r1_tarski(sK2,k6_partfun1(sK2)) | sK2 != k1_xboole_0 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_8882]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_11,plain,
% 12.00/1.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 12.00/1.97      inference(cnf_transformation,[],[f74]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1400,plain,
% 12.00/1.97      ( v1_xboole_0(X0) != iProver_top
% 12.00/1.97      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1393,plain,
% 12.00/1.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_12,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.00/1.97      | ~ v1_xboole_0(X1)
% 12.00/1.97      | v1_xboole_0(X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f75]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1399,plain,
% 12.00/1.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 12.00/1.97      | v1_xboole_0(X1) != iProver_top
% 12.00/1.97      | v1_xboole_0(X0) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3582,plain,
% 12.00/1.97      ( v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top
% 12.00/1.97      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_1393,c_1399]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5935,plain,
% 12.00/1.97      ( v1_xboole_0(X0) != iProver_top
% 12.00/1.97      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_1400,c_3582]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5936,plain,
% 12.00/1.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(k6_partfun1(X0)) ),
% 12.00/1.97      inference(predicate_to_equality_rev,[status(thm)],[c_5935]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5938,plain,
% 12.00/1.97      ( v1_xboole_0(k6_partfun1(sK2)) | ~ v1_xboole_0(sK2) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_5936]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1384,plain,
% 12.00/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1387,plain,
% 12.00/1.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_30,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 12.00/1.97      | ~ v1_funct_1(X0)
% 12.00/1.97      | ~ v1_funct_1(X3)
% 12.00/1.97      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f93]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1390,plain,
% 12.00/1.97      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 12.00/1.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 12.00/1.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.00/1.97      | v1_funct_1(X5) != iProver_top
% 12.00/1.97      | v1_funct_1(X4) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_4674,plain,
% 12.00/1.97      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 12.00/1.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.00/1.97      | v1_funct_1(X2) != iProver_top
% 12.00/1.97      | v1_funct_1(sK5) != iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_1387,c_1390]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_44,plain,
% 12.00/1.97      ( v1_funct_1(sK5) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_4995,plain,
% 12.00/1.97      ( v1_funct_1(X2) != iProver_top
% 12.00/1.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.00/1.97      | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
% 12.00/1.97      inference(global_propositional_subsumption,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_4674,c_44]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_4996,plain,
% 12.00/1.97      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 12.00/1.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.00/1.97      | v1_funct_1(X2) != iProver_top ),
% 12.00/1.97      inference(renaming,[status(thm)],[c_4995]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5007,plain,
% 12.00/1.97      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
% 12.00/1.97      | v1_funct_1(sK4) != iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_1384,c_4996]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1776,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 12.00/1.97      | ~ v1_funct_1(X0)
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_30]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2045,plain,
% 12.00/1.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.00/1.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | ~ v1_funct_1(sK5)
% 12.00/1.97      | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_1776]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2728,plain,
% 12.00/1.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.00/1.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | ~ v1_funct_1(sK5)
% 12.00/1.97      | k1_partfun1(X0,X1,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_2045]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_4336,plain,
% 12.00/1.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 12.00/1.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 12.00/1.97      | ~ v1_funct_1(sK4)
% 12.00/1.97      | ~ v1_funct_1(sK5)
% 12.00/1.97      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_2728]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5240,plain,
% 12.00/1.97      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 12.00/1.97      inference(global_propositional_subsumption,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_5007,c_40,c_38,c_37,c_35,c_4336]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1380,plain,
% 12.00/1.97      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 12.00/1.97      | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5243,plain,
% 12.00/1.97      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
% 12.00/1.97      | m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 12.00/1.97      inference(demodulation,[status(thm)],[c_5240,c_1380]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_41,plain,
% 12.00/1.97      ( v1_funct_1(sK4) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_43,plain,
% 12.00/1.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_46,plain,
% 12.00/1.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1392,plain,
% 12.00/1.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 12.00/1.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 12.00/1.97      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 12.00/1.97      | v1_funct_1(X0) != iProver_top
% 12.00/1.97      | v1_funct_1(X3) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5245,plain,
% 12.00/1.97      ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
% 12.00/1.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 12.00/1.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 12.00/1.97      | v1_funct_1(sK4) != iProver_top
% 12.00/1.97      | v1_funct_1(sK5) != iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_5240,c_1392]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5664,plain,
% 12.00/1.97      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
% 12.00/1.97      inference(global_propositional_subsumption,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_5243,c_41,c_43,c_44,c_46,c_5245]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5667,plain,
% 12.00/1.97      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
% 12.00/1.97      inference(demodulation,[status(thm)],[c_5664,c_5240]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1388,plain,
% 12.00/1.97      ( k1_xboole_0 = X0
% 12.00/1.97      | v1_funct_2(X1,X2,X0) != iProver_top
% 12.00/1.97      | v1_funct_2(X3,X4,X2) != iProver_top
% 12.00/1.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 12.00/1.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 12.00/1.97      | v1_funct_1(X1) != iProver_top
% 12.00/1.97      | v1_funct_1(X3) != iProver_top
% 12.00/1.97      | v2_funct_1(X3) = iProver_top
% 12.00/1.97      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5674,plain,
% 12.00/1.97      ( sK2 = k1_xboole_0
% 12.00/1.97      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 12.00/1.97      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 12.00/1.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 12.00/1.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 12.00/1.97      | v1_funct_1(sK4) != iProver_top
% 12.00/1.97      | v1_funct_1(sK5) != iProver_top
% 12.00/1.97      | v2_funct_1(k6_partfun1(sK2)) != iProver_top
% 12.00/1.97      | v2_funct_1(sK4) = iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_5667,c_1388]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_17,plain,
% 12.00/1.97      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 12.00/1.97      | ~ v1_relat_1(X0)
% 12.00/1.97      | ~ v1_relat_1(X1) ),
% 12.00/1.97      inference(cnf_transformation,[],[f80]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1396,plain,
% 12.00/1.97      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 12.00/1.97      | v1_relat_1(X0) != iProver_top
% 12.00/1.97      | v1_relat_1(X1) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5668,plain,
% 12.00/1.97      ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
% 12.00/1.97      | v1_relat_1(sK4) != iProver_top
% 12.00/1.97      | v1_relat_1(sK5) != iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_5664,c_1396]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_18,plain,
% 12.00/1.97      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 12.00/1.97      inference(cnf_transformation,[],[f105]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5669,plain,
% 12.00/1.97      ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
% 12.00/1.97      | v1_relat_1(sK4) != iProver_top
% 12.00/1.97      | v1_relat_1(sK5) != iProver_top ),
% 12.00/1.97      inference(demodulation,[status(thm)],[c_5668,c_18]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5608,plain,
% 12.00/1.97      ( ~ r2_hidden(sK1(sK4,X0),sK4) | ~ v1_xboole_0(sK4) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_1]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5610,plain,
% 12.00/1.97      ( ~ r2_hidden(sK1(sK4,sK2),sK4) | ~ v1_xboole_0(sK4) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_5608]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3584,plain,
% 12.00/1.97      ( v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 12.00/1.97      | v1_xboole_0(sK4) = iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_1384,c_1399]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3928,plain,
% 12.00/1.97      ( v1_xboole_0(sK4) = iProver_top
% 12.00/1.97      | v1_xboole_0(sK2) != iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_1400,c_3584]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3929,plain,
% 12.00/1.97      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK2) ),
% 12.00/1.97      inference(predicate_to_equality_rev,[status(thm)],[c_3928]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3,plain,
% 12.00/1.97      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f66]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3417,plain,
% 12.00/1.97      ( r1_tarski(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_3]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3419,plain,
% 12.00/1.97      ( r1_tarski(sK2,sK4) | r2_hidden(sK1(sK2,sK4),sK2) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_3417]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3329,plain,
% 12.00/1.97      ( r1_tarski(k6_partfun1(X0),X1)
% 12.00/1.97      | r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0)) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_3]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3331,plain,
% 12.00/1.97      ( r1_tarski(k6_partfun1(sK2),sK2)
% 12.00/1.97      | r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2)) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_3329]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_22,plain,
% 12.00/1.97      ( v5_relat_1(X0,X1)
% 12.00/1.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 12.00/1.97      inference(cnf_transformation,[],[f85]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_15,plain,
% 12.00/1.97      ( ~ v5_relat_1(X0,X1)
% 12.00/1.97      | r1_tarski(k2_relat_1(X0),X1)
% 12.00/1.97      | ~ v1_relat_1(X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f77]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_487,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.00/1.97      | r1_tarski(k2_relat_1(X0),X2)
% 12.00/1.97      | ~ v1_relat_1(X0) ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_22,c_15]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1379,plain,
% 12.00/1.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 12.00/1.97      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 12.00/1.97      | v1_relat_1(X0) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2801,plain,
% 12.00/1.97      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
% 12.00/1.97      | v1_relat_1(sK5) != iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_1387,c_1379]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_13,plain,
% 12.00/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.00/1.97      | ~ v1_relat_1(X1)
% 12.00/1.97      | v1_relat_1(X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f76]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2088,plain,
% 12.00/1.97      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK2)) | v1_relat_1(sK5) ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_13,c_35]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_16,plain,
% 12.00/1.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 12.00/1.97      inference(cnf_transformation,[],[f79]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2095,plain,
% 12.00/1.97      ( v1_relat_1(sK5) ),
% 12.00/1.97      inference(forward_subsumption_resolution,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_2088,c_16]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2096,plain,
% 12.00/1.97      ( v1_relat_1(sK5) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3067,plain,
% 12.00/1.97      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
% 12.00/1.97      inference(global_propositional_subsumption,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_2801,c_2096]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_5,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 12.00/1.97      inference(cnf_transformation,[],[f70]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1403,plain,
% 12.00/1.97      ( X0 = X1
% 12.00/1.97      | r1_tarski(X1,X0) != iProver_top
% 12.00/1.97      | r1_tarski(X0,X1) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_3072,plain,
% 12.00/1.97      ( k2_relat_1(sK5) = sK2
% 12.00/1.97      | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
% 12.00/1.97      inference(superposition,[status(thm)],[c_3067,c_1403]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2478,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_5]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2480,plain,
% 12.00/1.97      ( ~ r1_tarski(sK4,sK2) | ~ r1_tarski(sK2,sK4) | sK4 = sK2 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_2478]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2458,plain,
% 12.00/1.97      ( r1_tarski(sK4,X0) | r2_hidden(sK1(sK4,X0),sK4) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_3]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2460,plain,
% 12.00/1.97      ( r1_tarski(sK4,sK2) | r2_hidden(sK1(sK4,sK2),sK4) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_2458]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_14,plain,
% 12.00/1.97      ( v5_relat_1(X0,X1)
% 12.00/1.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 12.00/1.97      | ~ v1_relat_1(X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f78]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_26,plain,
% 12.00/1.97      ( v2_funct_2(X0,k2_relat_1(X0))
% 12.00/1.97      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 12.00/1.97      | ~ v1_relat_1(X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f113]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_33,negated_conjecture,
% 12.00/1.97      ( ~ v2_funct_2(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 12.00/1.97      inference(cnf_transformation,[],[f104]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_466,plain,
% 12.00/1.97      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 12.00/1.97      | ~ v2_funct_1(sK4)
% 12.00/1.97      | ~ v1_relat_1(X0)
% 12.00/1.97      | k2_relat_1(X0) != sK2
% 12.00/1.97      | sK5 != X0 ),
% 12.00/1.97      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_467,plain,
% 12.00/1.97      ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
% 12.00/1.97      | ~ v2_funct_1(sK4)
% 12.00/1.97      | ~ v1_relat_1(sK5)
% 12.00/1.97      | k2_relat_1(sK5) != sK2 ),
% 12.00/1.97      inference(unflattening,[status(thm)],[c_466]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_520,plain,
% 12.00/1.97      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 12.00/1.97      | ~ v2_funct_1(sK4)
% 12.00/1.97      | ~ v1_relat_1(X0)
% 12.00/1.97      | ~ v1_relat_1(sK5)
% 12.00/1.97      | k2_relat_1(sK5) != X1
% 12.00/1.97      | k2_relat_1(sK5) != sK2
% 12.00/1.97      | sK5 != X0 ),
% 12.00/1.97      inference(resolution_lifted,[status(thm)],[c_14,c_467]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_521,plain,
% 12.00/1.97      ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
% 12.00/1.97      | ~ v2_funct_1(sK4)
% 12.00/1.97      | ~ v1_relat_1(sK5)
% 12.00/1.97      | k2_relat_1(sK5) != sK2 ),
% 12.00/1.97      inference(unflattening,[status(thm)],[c_520]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_6,plain,
% 12.00/1.97      ( r1_tarski(X0,X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f110]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_531,plain,
% 12.00/1.97      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK5) | k2_relat_1(sK5) != sK2 ),
% 12.00/1.97      inference(forward_subsumption_resolution,[status(thm)],[c_521,c_6]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2371,plain,
% 12.00/1.97      ( ~ v2_funct_1(sK4) | k2_relat_1(sK5) != sK2 ),
% 12.00/1.97      inference(backward_subsumption_resolution,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_2095,c_531]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2090,plain,
% 12.00/1.97      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) | v1_relat_1(sK4) ),
% 12.00/1.97      inference(resolution,[status(thm)],[c_13,c_38]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2102,plain,
% 12.00/1.97      ( v1_relat_1(sK4) ),
% 12.00/1.97      inference(forward_subsumption_resolution,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_2090,c_16]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_2103,plain,
% 12.00/1.97      ( v1_relat_1(sK4) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_2102]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1892,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,k6_partfun1(X1))
% 12.00/1.97      | ~ r1_tarski(k6_partfun1(X1),X0)
% 12.00/1.97      | X0 = k6_partfun1(X1) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_5]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1894,plain,
% 12.00/1.97      ( ~ r1_tarski(k6_partfun1(sK2),sK2)
% 12.00/1.97      | ~ r1_tarski(sK2,k6_partfun1(sK2))
% 12.00/1.97      | sK2 = k6_partfun1(sK2) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_1892]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1679,plain,
% 12.00/1.97      ( v2_funct_1(X0)
% 12.00/1.97      | ~ v2_funct_1(k6_partfun1(X1))
% 12.00/1.97      | X0 != k6_partfun1(X1) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_767]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_1681,plain,
% 12.00/1.97      ( ~ v2_funct_1(k6_partfun1(sK2))
% 12.00/1.97      | v2_funct_1(sK2)
% 12.00/1.97      | sK2 != k6_partfun1(sK2) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_1679]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_532,plain,
% 12.00/1.97      ( k2_relat_1(sK5) != sK2
% 12.00/1.97      | v2_funct_1(sK4) != iProver_top
% 12.00/1.97      | v1_relat_1(sK5) != iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_9,plain,
% 12.00/1.97      ( r1_xboole_0(X0,k1_xboole_0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f72]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_10,plain,
% 12.00/1.97      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f73]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_430,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,X1)
% 12.00/1.97      | v1_xboole_0(X0)
% 12.00/1.97      | X0 != X2
% 12.00/1.97      | k1_xboole_0 != X1 ),
% 12.00/1.97      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_431,plain,
% 12.00/1.97      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 12.00/1.97      inference(unflattening,[status(thm)],[c_430]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_433,plain,
% 12.00/1.97      ( ~ r1_tarski(sK2,k1_xboole_0) | v1_xboole_0(sK2) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_431]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_121,plain,
% 12.00/1.97      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_5]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_7,plain,
% 12.00/1.97      ( r1_tarski(X0,X0) ),
% 12.00/1.97      inference(cnf_transformation,[],[f111]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_117,plain,
% 12.00/1.97      ( r1_tarski(sK2,sK2) ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_7]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_85,plain,
% 12.00/1.97      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_87,plain,
% 12.00/1.97      ( v2_funct_1(k6_partfun1(sK2)) = iProver_top ),
% 12.00/1.97      inference(instantiation,[status(thm)],[c_85]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_36,negated_conjecture,
% 12.00/1.97      ( v1_funct_2(sK5,sK3,sK2) ),
% 12.00/1.97      inference(cnf_transformation,[],[f101]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_45,plain,
% 12.00/1.97      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_39,negated_conjecture,
% 12.00/1.97      ( v1_funct_2(sK4,sK2,sK3) ),
% 12.00/1.97      inference(cnf_transformation,[],[f98]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(c_42,plain,
% 12.00/1.97      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 12.00/1.97      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 12.00/1.97  
% 12.00/1.97  cnf(contradiction,plain,
% 12.00/1.97      ( $false ),
% 12.00/1.97      inference(minisat,
% 12.00/1.97                [status(thm)],
% 12.00/1.97                [c_48188,c_18586,c_13541,c_11103,c_9097,c_8884,c_5938,
% 12.00/1.97                 c_5674,c_5669,c_5610,c_3929,c_3419,c_3331,c_3072,c_2480,
% 12.00/1.97                 c_2460,c_2371,c_2103,c_2096,c_1894,c_1681,c_532,c_433,
% 12.00/1.97                 c_121,c_117,c_87,c_86,c_46,c_35,c_45,c_36,c_44,c_37,
% 12.00/1.97                 c_43,c_38,c_42,c_39,c_41,c_40]) ).
% 12.00/1.97  
% 12.00/1.97  
% 12.00/1.97  % SZS output end CNFRefutation for theBenchmark.p
% 12.00/1.97  
% 12.00/1.97  ------                               Statistics
% 12.00/1.97  
% 12.00/1.97  ------ Selected
% 12.00/1.97  
% 12.00/1.97  total_time:                             1.335
% 12.00/1.97  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:02 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 802 expanded)
%              Number of clauses        :   98 ( 261 expanded)
%              Number of leaves         :   22 ( 193 expanded)
%              Depth                    :   18
%              Number of atoms          :  595 (5005 expanded)
%              Number of equality atoms :  152 ( 360 expanded)
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

fof(f66,plain,(
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

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f48,f47])).

fof(f78,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f70,plain,(
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

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f60,plain,(
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

fof(f69,plain,(
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

fof(f73,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f59,plain,(
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

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f68])).

cnf(c_737,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_2735,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(sK3)
    | sK3 != X0_50 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_2737,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(sK1)
    | sK3 != sK1 ),
    inference(instantiation,[status(thm)],[c_2735])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | m1_subset_1(k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1170,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) = iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_483,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_47,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_485,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_47])).

cnf(c_705,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_485])).

cnf(c_1185,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_2143,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1185])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2472,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_29,c_31,c_32,c_34])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_715,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v2_funct_1(X3_50)
    | ~ v2_funct_1(k1_partfun1(X4_50,X1_50,X1_50,X2_50,X3_50,X0_50))
    | k1_xboole_0 = X2_50 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1174,plain,
    ( k1_xboole_0 = X0_50
    | v1_funct_2(X1_50,X2_50,X0_50) != iProver_top
    | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X0_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v2_funct_1(X3_50) = iProver_top
    | v2_funct_1(k1_partfun1(X4_50,X2_50,X2_50,X0_50,X3_50,X1_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_2498,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2472,c_1174])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_327])).

cnf(c_1842,plain,
    ( ~ m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(X1_50))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(k6_partfun1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_2441,plain,
    ( ~ m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_xboole_0(k2_zfmisc_1(X1_50,X2_50))
    | v1_xboole_0(k6_partfun1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_2443,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK1))
    | v1_xboole_0(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_714,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1175,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1169,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_2055,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1175,c_1169])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_496,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_573,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_497])).

cnf(c_704,plain,
    ( ~ v1_funct_2(X0_50,X1_50,sK1)
    | ~ v1_funct_2(X2_50,sK1,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1)))
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X1_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X2_50)
    | k1_partfun1(sK1,X1_50,X1_50,sK1,X2_50,X0_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1_50,sK1,X0_50) = sK1 ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_1186,plain,
    ( k1_partfun1(sK1,X0_50,X0_50,sK1,X1_50,X2_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0_50,sK1,X2_50) = sK1
    | v1_funct_2(X2_50,X0_50,sK1) != iProver_top
    | v1_funct_2(X1_50,sK1,X0_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_1829,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1186])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1832,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1829,c_29,c_30,c_31,c_32,c_33,c_34])).

cnf(c_2068,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2055,c_1832])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_400,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_401,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_411,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_401,c_8])).

cnf(c_21,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_21])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_707,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_726,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_707])).

cnf(c_1183,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2326,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2068,c_1183])).

cnf(c_2384,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_2326])).

cnf(c_2390,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2384])).

cnf(c_727,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_707])).

cnf(c_1182,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_2327,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2068,c_1182])).

cnf(c_2328,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2327])).

cnf(c_732,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_2248,plain,
    ( v1_xboole_0(X0_50)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_50 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_2250,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_722,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2121,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | ~ v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1734,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_50))
    | ~ v1_xboole_0(X0_50)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_2019,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_724,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(X1_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1779,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0_50 ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1781,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK1)
    | sK3 = sK1 ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_1604,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(k6_partfun1(X1_50))
    | X0_50 = k6_partfun1(X1_50) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1606,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK1))
    | ~ v1_xboole_0(sK1)
    | sK1 = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1394,plain,
    ( v2_funct_1(X0_50)
    | ~ v2_funct_1(k6_partfun1(X1_50))
    | X0_50 != k6_partfun1(X1_50) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1396,plain,
    ( ~ v2_funct_1(k6_partfun1(sK1))
    | v2_funct_1(sK1)
    | sK1 != k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_83,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK1))
    | ~ v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_76,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_78,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_77,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2737,c_2498,c_2443,c_2390,c_2384,c_2328,c_2250,c_2121,c_2068,c_2019,c_1781,c_1606,c_1396,c_727,c_2,c_83,c_78,c_77,c_47,c_34,c_33,c_32,c_31,c_26,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:24 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.77/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.01  
% 2.77/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/1.01  
% 2.77/1.01  ------  iProver source info
% 2.77/1.01  
% 2.77/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.77/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/1.01  git: non_committed_changes: false
% 2.77/1.01  git: last_make_outside_of_git: false
% 2.77/1.01  
% 2.77/1.01  ------ 
% 2.77/1.01  
% 2.77/1.01  ------ Input Options
% 2.77/1.01  
% 2.77/1.01  --out_options                           all
% 2.77/1.01  --tptp_safe_out                         true
% 2.77/1.01  --problem_path                          ""
% 2.77/1.01  --include_path                          ""
% 2.77/1.01  --clausifier                            res/vclausify_rel
% 2.77/1.01  --clausifier_options                    --mode clausify
% 2.77/1.01  --stdin                                 false
% 2.77/1.01  --stats_out                             all
% 2.77/1.01  
% 2.77/1.01  ------ General Options
% 2.77/1.01  
% 2.77/1.01  --fof                                   false
% 2.77/1.01  --time_out_real                         305.
% 2.77/1.01  --time_out_virtual                      -1.
% 2.77/1.01  --symbol_type_check                     false
% 2.77/1.01  --clausify_out                          false
% 2.77/1.01  --sig_cnt_out                           false
% 2.77/1.01  --trig_cnt_out                          false
% 2.77/1.01  --trig_cnt_out_tolerance                1.
% 2.77/1.01  --trig_cnt_out_sk_spl                   false
% 2.77/1.01  --abstr_cl_out                          false
% 2.77/1.01  
% 2.77/1.01  ------ Global Options
% 2.77/1.01  
% 2.77/1.01  --schedule                              default
% 2.77/1.01  --add_important_lit                     false
% 2.77/1.01  --prop_solver_per_cl                    1000
% 2.77/1.01  --min_unsat_core                        false
% 2.77/1.01  --soft_assumptions                      false
% 2.77/1.01  --soft_lemma_size                       3
% 2.77/1.01  --prop_impl_unit_size                   0
% 2.77/1.01  --prop_impl_unit                        []
% 2.77/1.01  --share_sel_clauses                     true
% 2.77/1.01  --reset_solvers                         false
% 2.77/1.01  --bc_imp_inh                            [conj_cone]
% 2.77/1.01  --conj_cone_tolerance                   3.
% 2.77/1.01  --extra_neg_conj                        none
% 2.77/1.01  --large_theory_mode                     true
% 2.77/1.01  --prolific_symb_bound                   200
% 2.77/1.01  --lt_threshold                          2000
% 2.77/1.01  --clause_weak_htbl                      true
% 2.77/1.01  --gc_record_bc_elim                     false
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing Options
% 2.77/1.01  
% 2.77/1.01  --preprocessing_flag                    true
% 2.77/1.01  --time_out_prep_mult                    0.1
% 2.77/1.01  --splitting_mode                        input
% 2.77/1.01  --splitting_grd                         true
% 2.77/1.01  --splitting_cvd                         false
% 2.77/1.01  --splitting_cvd_svl                     false
% 2.77/1.01  --splitting_nvd                         32
% 2.77/1.01  --sub_typing                            true
% 2.77/1.01  --prep_gs_sim                           true
% 2.77/1.01  --prep_unflatten                        true
% 2.77/1.01  --prep_res_sim                          true
% 2.77/1.01  --prep_upred                            true
% 2.77/1.01  --prep_sem_filter                       exhaustive
% 2.77/1.01  --prep_sem_filter_out                   false
% 2.77/1.01  --pred_elim                             true
% 2.77/1.01  --res_sim_input                         true
% 2.77/1.01  --eq_ax_congr_red                       true
% 2.77/1.01  --pure_diseq_elim                       true
% 2.77/1.01  --brand_transform                       false
% 2.77/1.01  --non_eq_to_eq                          false
% 2.77/1.01  --prep_def_merge                        true
% 2.77/1.01  --prep_def_merge_prop_impl              false
% 2.77/1.01  --prep_def_merge_mbd                    true
% 2.77/1.01  --prep_def_merge_tr_red                 false
% 2.77/1.01  --prep_def_merge_tr_cl                  false
% 2.77/1.01  --smt_preprocessing                     true
% 2.77/1.01  --smt_ac_axioms                         fast
% 2.77/1.01  --preprocessed_out                      false
% 2.77/1.01  --preprocessed_stats                    false
% 2.77/1.01  
% 2.77/1.01  ------ Abstraction refinement Options
% 2.77/1.01  
% 2.77/1.01  --abstr_ref                             []
% 2.77/1.01  --abstr_ref_prep                        false
% 2.77/1.01  --abstr_ref_until_sat                   false
% 2.77/1.01  --abstr_ref_sig_restrict                funpre
% 2.77/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.01  --abstr_ref_under                       []
% 2.77/1.01  
% 2.77/1.01  ------ SAT Options
% 2.77/1.01  
% 2.77/1.01  --sat_mode                              false
% 2.77/1.01  --sat_fm_restart_options                ""
% 2.77/1.01  --sat_gr_def                            false
% 2.77/1.01  --sat_epr_types                         true
% 2.77/1.01  --sat_non_cyclic_types                  false
% 2.77/1.01  --sat_finite_models                     false
% 2.77/1.01  --sat_fm_lemmas                         false
% 2.77/1.01  --sat_fm_prep                           false
% 2.77/1.01  --sat_fm_uc_incr                        true
% 2.77/1.01  --sat_out_model                         small
% 2.77/1.01  --sat_out_clauses                       false
% 2.77/1.01  
% 2.77/1.01  ------ QBF Options
% 2.77/1.01  
% 2.77/1.01  --qbf_mode                              false
% 2.77/1.01  --qbf_elim_univ                         false
% 2.77/1.01  --qbf_dom_inst                          none
% 2.77/1.01  --qbf_dom_pre_inst                      false
% 2.77/1.01  --qbf_sk_in                             false
% 2.77/1.01  --qbf_pred_elim                         true
% 2.77/1.01  --qbf_split                             512
% 2.77/1.01  
% 2.77/1.01  ------ BMC1 Options
% 2.77/1.01  
% 2.77/1.01  --bmc1_incremental                      false
% 2.77/1.01  --bmc1_axioms                           reachable_all
% 2.77/1.01  --bmc1_min_bound                        0
% 2.77/1.01  --bmc1_max_bound                        -1
% 2.77/1.01  --bmc1_max_bound_default                -1
% 2.77/1.01  --bmc1_symbol_reachability              true
% 2.77/1.01  --bmc1_property_lemmas                  false
% 2.77/1.01  --bmc1_k_induction                      false
% 2.77/1.01  --bmc1_non_equiv_states                 false
% 2.77/1.01  --bmc1_deadlock                         false
% 2.77/1.01  --bmc1_ucm                              false
% 2.77/1.01  --bmc1_add_unsat_core                   none
% 2.77/1.01  --bmc1_unsat_core_children              false
% 2.77/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.01  --bmc1_out_stat                         full
% 2.77/1.01  --bmc1_ground_init                      false
% 2.77/1.01  --bmc1_pre_inst_next_state              false
% 2.77/1.01  --bmc1_pre_inst_state                   false
% 2.77/1.01  --bmc1_pre_inst_reach_state             false
% 2.77/1.01  --bmc1_out_unsat_core                   false
% 2.77/1.01  --bmc1_aig_witness_out                  false
% 2.77/1.01  --bmc1_verbose                          false
% 2.77/1.01  --bmc1_dump_clauses_tptp                false
% 2.77/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.01  --bmc1_dump_file                        -
% 2.77/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.01  --bmc1_ucm_extend_mode                  1
% 2.77/1.01  --bmc1_ucm_init_mode                    2
% 2.77/1.01  --bmc1_ucm_cone_mode                    none
% 2.77/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.01  --bmc1_ucm_relax_model                  4
% 2.77/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.01  --bmc1_ucm_layered_model                none
% 2.77/1.01  --bmc1_ucm_max_lemma_size               10
% 2.77/1.01  
% 2.77/1.01  ------ AIG Options
% 2.77/1.01  
% 2.77/1.01  --aig_mode                              false
% 2.77/1.01  
% 2.77/1.01  ------ Instantiation Options
% 2.77/1.01  
% 2.77/1.01  --instantiation_flag                    true
% 2.77/1.01  --inst_sos_flag                         false
% 2.77/1.01  --inst_sos_phase                        true
% 2.77/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.01  --inst_lit_sel_side                     num_symb
% 2.77/1.01  --inst_solver_per_active                1400
% 2.77/1.01  --inst_solver_calls_frac                1.
% 2.77/1.01  --inst_passive_queue_type               priority_queues
% 2.77/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.01  --inst_passive_queues_freq              [25;2]
% 2.77/1.01  --inst_dismatching                      true
% 2.77/1.01  --inst_eager_unprocessed_to_passive     true
% 2.77/1.01  --inst_prop_sim_given                   true
% 2.77/1.01  --inst_prop_sim_new                     false
% 2.77/1.01  --inst_subs_new                         false
% 2.77/1.01  --inst_eq_res_simp                      false
% 2.77/1.01  --inst_subs_given                       false
% 2.77/1.01  --inst_orphan_elimination               true
% 2.77/1.01  --inst_learning_loop_flag               true
% 2.77/1.01  --inst_learning_start                   3000
% 2.77/1.01  --inst_learning_factor                  2
% 2.77/1.01  --inst_start_prop_sim_after_learn       3
% 2.77/1.01  --inst_sel_renew                        solver
% 2.77/1.01  --inst_lit_activity_flag                true
% 2.77/1.01  --inst_restr_to_given                   false
% 2.77/1.01  --inst_activity_threshold               500
% 2.77/1.01  --inst_out_proof                        true
% 2.77/1.01  
% 2.77/1.01  ------ Resolution Options
% 2.77/1.01  
% 2.77/1.01  --resolution_flag                       true
% 2.77/1.01  --res_lit_sel                           adaptive
% 2.77/1.01  --res_lit_sel_side                      none
% 2.77/1.01  --res_ordering                          kbo
% 2.77/1.01  --res_to_prop_solver                    active
% 2.77/1.01  --res_prop_simpl_new                    false
% 2.77/1.01  --res_prop_simpl_given                  true
% 2.77/1.01  --res_passive_queue_type                priority_queues
% 2.77/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.01  --res_passive_queues_freq               [15;5]
% 2.77/1.01  --res_forward_subs                      full
% 2.77/1.01  --res_backward_subs                     full
% 2.77/1.01  --res_forward_subs_resolution           true
% 2.77/1.01  --res_backward_subs_resolution          true
% 2.77/1.01  --res_orphan_elimination                true
% 2.77/1.01  --res_time_limit                        2.
% 2.77/1.01  --res_out_proof                         true
% 2.77/1.01  
% 2.77/1.01  ------ Superposition Options
% 2.77/1.01  
% 2.77/1.01  --superposition_flag                    true
% 2.77/1.01  --sup_passive_queue_type                priority_queues
% 2.77/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.01  --demod_completeness_check              fast
% 2.77/1.01  --demod_use_ground                      true
% 2.77/1.01  --sup_to_prop_solver                    passive
% 2.77/1.01  --sup_prop_simpl_new                    true
% 2.77/1.01  --sup_prop_simpl_given                  true
% 2.77/1.01  --sup_fun_splitting                     false
% 2.77/1.01  --sup_smt_interval                      50000
% 2.77/1.01  
% 2.77/1.01  ------ Superposition Simplification Setup
% 2.77/1.01  
% 2.77/1.01  --sup_indices_passive                   []
% 2.77/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.01  --sup_full_bw                           [BwDemod]
% 2.77/1.01  --sup_immed_triv                        [TrivRules]
% 2.77/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.01  --sup_immed_bw_main                     []
% 2.77/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.01  
% 2.77/1.01  ------ Combination Options
% 2.77/1.01  
% 2.77/1.01  --comb_res_mult                         3
% 2.77/1.01  --comb_sup_mult                         2
% 2.77/1.01  --comb_inst_mult                        10
% 2.77/1.01  
% 2.77/1.01  ------ Debug Options
% 2.77/1.01  
% 2.77/1.01  --dbg_backtrace                         false
% 2.77/1.01  --dbg_dump_prop_clauses                 false
% 2.77/1.01  --dbg_dump_prop_clauses_file            -
% 2.77/1.01  --dbg_out_stat                          false
% 2.77/1.01  ------ Parsing...
% 2.77/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.01  ------ Proving...
% 2.77/1.01  ------ Problem Properties 
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  clauses                                 23
% 2.77/1.01  conjectures                             6
% 2.77/1.01  EPR                                     6
% 2.77/1.01  Horn                                    22
% 2.77/1.01  unary                                   9
% 2.77/1.01  binary                                  5
% 2.77/1.01  lits                                    71
% 2.77/1.01  lits eq                                 9
% 2.77/1.01  fd_pure                                 0
% 2.77/1.01  fd_pseudo                               0
% 2.77/1.01  fd_cond                                 1
% 2.77/1.01  fd_pseudo_cond                          1
% 2.77/1.01  AC symbols                              0
% 2.77/1.01  
% 2.77/1.01  ------ Schedule dynamic 5 is on 
% 2.77/1.01  
% 2.77/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  ------ 
% 2.77/1.01  Current options:
% 2.77/1.01  ------ 
% 2.77/1.01  
% 2.77/1.01  ------ Input Options
% 2.77/1.01  
% 2.77/1.01  --out_options                           all
% 2.77/1.01  --tptp_safe_out                         true
% 2.77/1.01  --problem_path                          ""
% 2.77/1.01  --include_path                          ""
% 2.77/1.01  --clausifier                            res/vclausify_rel
% 2.77/1.01  --clausifier_options                    --mode clausify
% 2.77/1.01  --stdin                                 false
% 2.77/1.01  --stats_out                             all
% 2.77/1.02  
% 2.77/1.02  ------ General Options
% 2.77/1.02  
% 2.77/1.02  --fof                                   false
% 2.77/1.02  --time_out_real                         305.
% 2.77/1.02  --time_out_virtual                      -1.
% 2.77/1.02  --symbol_type_check                     false
% 2.77/1.02  --clausify_out                          false
% 2.77/1.02  --sig_cnt_out                           false
% 2.77/1.02  --trig_cnt_out                          false
% 2.77/1.02  --trig_cnt_out_tolerance                1.
% 2.77/1.02  --trig_cnt_out_sk_spl                   false
% 2.77/1.02  --abstr_cl_out                          false
% 2.77/1.02  
% 2.77/1.02  ------ Global Options
% 2.77/1.02  
% 2.77/1.02  --schedule                              default
% 2.77/1.02  --add_important_lit                     false
% 2.77/1.02  --prop_solver_per_cl                    1000
% 2.77/1.02  --min_unsat_core                        false
% 2.77/1.02  --soft_assumptions                      false
% 2.77/1.02  --soft_lemma_size                       3
% 2.77/1.02  --prop_impl_unit_size                   0
% 2.77/1.02  --prop_impl_unit                        []
% 2.77/1.02  --share_sel_clauses                     true
% 2.77/1.02  --reset_solvers                         false
% 2.77/1.02  --bc_imp_inh                            [conj_cone]
% 2.77/1.02  --conj_cone_tolerance                   3.
% 2.77/1.02  --extra_neg_conj                        none
% 2.77/1.02  --large_theory_mode                     true
% 2.77/1.02  --prolific_symb_bound                   200
% 2.77/1.02  --lt_threshold                          2000
% 2.77/1.02  --clause_weak_htbl                      true
% 2.77/1.02  --gc_record_bc_elim                     false
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing Options
% 2.77/1.02  
% 2.77/1.02  --preprocessing_flag                    true
% 2.77/1.02  --time_out_prep_mult                    0.1
% 2.77/1.02  --splitting_mode                        input
% 2.77/1.02  --splitting_grd                         true
% 2.77/1.02  --splitting_cvd                         false
% 2.77/1.02  --splitting_cvd_svl                     false
% 2.77/1.02  --splitting_nvd                         32
% 2.77/1.02  --sub_typing                            true
% 2.77/1.02  --prep_gs_sim                           true
% 2.77/1.02  --prep_unflatten                        true
% 2.77/1.02  --prep_res_sim                          true
% 2.77/1.02  --prep_upred                            true
% 2.77/1.02  --prep_sem_filter                       exhaustive
% 2.77/1.02  --prep_sem_filter_out                   false
% 2.77/1.02  --pred_elim                             true
% 2.77/1.02  --res_sim_input                         true
% 2.77/1.02  --eq_ax_congr_red                       true
% 2.77/1.02  --pure_diseq_elim                       true
% 2.77/1.02  --brand_transform                       false
% 2.77/1.02  --non_eq_to_eq                          false
% 2.77/1.02  --prep_def_merge                        true
% 2.77/1.02  --prep_def_merge_prop_impl              false
% 2.77/1.02  --prep_def_merge_mbd                    true
% 2.77/1.02  --prep_def_merge_tr_red                 false
% 2.77/1.02  --prep_def_merge_tr_cl                  false
% 2.77/1.02  --smt_preprocessing                     true
% 2.77/1.02  --smt_ac_axioms                         fast
% 2.77/1.02  --preprocessed_out                      false
% 2.77/1.02  --preprocessed_stats                    false
% 2.77/1.02  
% 2.77/1.02  ------ Abstraction refinement Options
% 2.77/1.02  
% 2.77/1.02  --abstr_ref                             []
% 2.77/1.02  --abstr_ref_prep                        false
% 2.77/1.02  --abstr_ref_until_sat                   false
% 2.77/1.02  --abstr_ref_sig_restrict                funpre
% 2.77/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.02  --abstr_ref_under                       []
% 2.77/1.02  
% 2.77/1.02  ------ SAT Options
% 2.77/1.02  
% 2.77/1.02  --sat_mode                              false
% 2.77/1.02  --sat_fm_restart_options                ""
% 2.77/1.02  --sat_gr_def                            false
% 2.77/1.02  --sat_epr_types                         true
% 2.77/1.02  --sat_non_cyclic_types                  false
% 2.77/1.02  --sat_finite_models                     false
% 2.77/1.02  --sat_fm_lemmas                         false
% 2.77/1.02  --sat_fm_prep                           false
% 2.77/1.02  --sat_fm_uc_incr                        true
% 2.77/1.02  --sat_out_model                         small
% 2.77/1.02  --sat_out_clauses                       false
% 2.77/1.02  
% 2.77/1.02  ------ QBF Options
% 2.77/1.02  
% 2.77/1.02  --qbf_mode                              false
% 2.77/1.02  --qbf_elim_univ                         false
% 2.77/1.02  --qbf_dom_inst                          none
% 2.77/1.02  --qbf_dom_pre_inst                      false
% 2.77/1.02  --qbf_sk_in                             false
% 2.77/1.02  --qbf_pred_elim                         true
% 2.77/1.02  --qbf_split                             512
% 2.77/1.02  
% 2.77/1.02  ------ BMC1 Options
% 2.77/1.02  
% 2.77/1.02  --bmc1_incremental                      false
% 2.77/1.02  --bmc1_axioms                           reachable_all
% 2.77/1.02  --bmc1_min_bound                        0
% 2.77/1.02  --bmc1_max_bound                        -1
% 2.77/1.02  --bmc1_max_bound_default                -1
% 2.77/1.02  --bmc1_symbol_reachability              true
% 2.77/1.02  --bmc1_property_lemmas                  false
% 2.77/1.02  --bmc1_k_induction                      false
% 2.77/1.02  --bmc1_non_equiv_states                 false
% 2.77/1.02  --bmc1_deadlock                         false
% 2.77/1.02  --bmc1_ucm                              false
% 2.77/1.02  --bmc1_add_unsat_core                   none
% 2.77/1.02  --bmc1_unsat_core_children              false
% 2.77/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.02  --bmc1_out_stat                         full
% 2.77/1.02  --bmc1_ground_init                      false
% 2.77/1.02  --bmc1_pre_inst_next_state              false
% 2.77/1.02  --bmc1_pre_inst_state                   false
% 2.77/1.02  --bmc1_pre_inst_reach_state             false
% 2.77/1.02  --bmc1_out_unsat_core                   false
% 2.77/1.02  --bmc1_aig_witness_out                  false
% 2.77/1.02  --bmc1_verbose                          false
% 2.77/1.02  --bmc1_dump_clauses_tptp                false
% 2.77/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.02  --bmc1_dump_file                        -
% 2.77/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.02  --bmc1_ucm_extend_mode                  1
% 2.77/1.02  --bmc1_ucm_init_mode                    2
% 2.77/1.02  --bmc1_ucm_cone_mode                    none
% 2.77/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.02  --bmc1_ucm_relax_model                  4
% 2.77/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.02  --bmc1_ucm_layered_model                none
% 2.77/1.02  --bmc1_ucm_max_lemma_size               10
% 2.77/1.02  
% 2.77/1.02  ------ AIG Options
% 2.77/1.02  
% 2.77/1.02  --aig_mode                              false
% 2.77/1.02  
% 2.77/1.02  ------ Instantiation Options
% 2.77/1.02  
% 2.77/1.02  --instantiation_flag                    true
% 2.77/1.02  --inst_sos_flag                         false
% 2.77/1.02  --inst_sos_phase                        true
% 2.77/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel_side                     none
% 2.77/1.02  --inst_solver_per_active                1400
% 2.77/1.02  --inst_solver_calls_frac                1.
% 2.77/1.02  --inst_passive_queue_type               priority_queues
% 2.77/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.02  --inst_passive_queues_freq              [25;2]
% 2.77/1.02  --inst_dismatching                      true
% 2.77/1.02  --inst_eager_unprocessed_to_passive     true
% 2.77/1.02  --inst_prop_sim_given                   true
% 2.77/1.02  --inst_prop_sim_new                     false
% 2.77/1.02  --inst_subs_new                         false
% 2.77/1.02  --inst_eq_res_simp                      false
% 2.77/1.02  --inst_subs_given                       false
% 2.77/1.02  --inst_orphan_elimination               true
% 2.77/1.02  --inst_learning_loop_flag               true
% 2.77/1.02  --inst_learning_start                   3000
% 2.77/1.02  --inst_learning_factor                  2
% 2.77/1.02  --inst_start_prop_sim_after_learn       3
% 2.77/1.02  --inst_sel_renew                        solver
% 2.77/1.02  --inst_lit_activity_flag                true
% 2.77/1.02  --inst_restr_to_given                   false
% 2.77/1.02  --inst_activity_threshold               500
% 2.77/1.02  --inst_out_proof                        true
% 2.77/1.02  
% 2.77/1.02  ------ Resolution Options
% 2.77/1.02  
% 2.77/1.02  --resolution_flag                       false
% 2.77/1.02  --res_lit_sel                           adaptive
% 2.77/1.02  --res_lit_sel_side                      none
% 2.77/1.02  --res_ordering                          kbo
% 2.77/1.02  --res_to_prop_solver                    active
% 2.77/1.02  --res_prop_simpl_new                    false
% 2.77/1.02  --res_prop_simpl_given                  true
% 2.77/1.02  --res_passive_queue_type                priority_queues
% 2.77/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.02  --res_passive_queues_freq               [15;5]
% 2.77/1.02  --res_forward_subs                      full
% 2.77/1.02  --res_backward_subs                     full
% 2.77/1.02  --res_forward_subs_resolution           true
% 2.77/1.02  --res_backward_subs_resolution          true
% 2.77/1.02  --res_orphan_elimination                true
% 2.77/1.02  --res_time_limit                        2.
% 2.77/1.02  --res_out_proof                         true
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Options
% 2.77/1.02  
% 2.77/1.02  --superposition_flag                    true
% 2.77/1.02  --sup_passive_queue_type                priority_queues
% 2.77/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.02  --demod_completeness_check              fast
% 2.77/1.02  --demod_use_ground                      true
% 2.77/1.02  --sup_to_prop_solver                    passive
% 2.77/1.02  --sup_prop_simpl_new                    true
% 2.77/1.02  --sup_prop_simpl_given                  true
% 2.77/1.02  --sup_fun_splitting                     false
% 2.77/1.02  --sup_smt_interval                      50000
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Simplification Setup
% 2.77/1.02  
% 2.77/1.02  --sup_indices_passive                   []
% 2.77/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_full_bw                           [BwDemod]
% 2.77/1.02  --sup_immed_triv                        [TrivRules]
% 2.77/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_immed_bw_main                     []
% 2.77/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  
% 2.77/1.02  ------ Combination Options
% 2.77/1.02  
% 2.77/1.02  --comb_res_mult                         3
% 2.77/1.02  --comb_sup_mult                         2
% 2.77/1.02  --comb_inst_mult                        10
% 2.77/1.02  
% 2.77/1.02  ------ Debug Options
% 2.77/1.02  
% 2.77/1.02  --dbg_backtrace                         false
% 2.77/1.02  --dbg_dump_prop_clauses                 false
% 2.77/1.02  --dbg_dump_prop_clauses_file            -
% 2.77/1.02  --dbg_out_stat                          false
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  ------ Proving...
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  % SZS status Theorem for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  fof(f13,axiom,(
% 2.77/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f33,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.77/1.02    inference(ennf_transformation,[],[f13])).
% 2.77/1.02  
% 2.77/1.02  fof(f34,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.77/1.02    inference(flattening,[],[f33])).
% 2.77/1.02  
% 2.77/1.02  fof(f66,plain,(
% 2.77/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f34])).
% 2.77/1.02  
% 2.77/1.02  fof(f11,axiom,(
% 2.77/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f29,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.77/1.02    inference(ennf_transformation,[],[f11])).
% 2.77/1.02  
% 2.77/1.02  fof(f30,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(flattening,[],[f29])).
% 2.77/1.02  
% 2.77/1.02  fof(f45,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(nnf_transformation,[],[f30])).
% 2.77/1.02  
% 2.77/1.02  fof(f61,plain,(
% 2.77/1.02    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f45])).
% 2.77/1.02  
% 2.77/1.02  fof(f18,conjecture,(
% 2.77/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f19,negated_conjecture,(
% 2.77/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.77/1.02    inference(negated_conjecture,[],[f18])).
% 2.77/1.02  
% 2.77/1.02  fof(f39,plain,(
% 2.77/1.02    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.77/1.02    inference(ennf_transformation,[],[f19])).
% 2.77/1.02  
% 2.77/1.02  fof(f40,plain,(
% 2.77/1.02    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.77/1.02    inference(flattening,[],[f39])).
% 2.77/1.02  
% 2.77/1.02  fof(f48,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f47,plain,(
% 2.77/1.02    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f49,plain,(
% 2.77/1.02    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 2.77/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f40,f48,f47])).
% 2.77/1.02  
% 2.77/1.02  fof(f78,plain,(
% 2.77/1.02    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f14,axiom,(
% 2.77/1.02    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f20,plain,(
% 2.77/1.02    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.77/1.02    inference(pure_predicate_removal,[],[f14])).
% 2.77/1.02  
% 2.77/1.02  fof(f67,plain,(
% 2.77/1.02    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f20])).
% 2.77/1.02  
% 2.77/1.02  fof(f72,plain,(
% 2.77/1.02    v1_funct_1(sK3)),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f74,plain,(
% 2.77/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f75,plain,(
% 2.77/1.02    v1_funct_1(sK4)),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f77,plain,(
% 2.77/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f17,axiom,(
% 2.77/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f37,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.77/1.02    inference(ennf_transformation,[],[f17])).
% 2.77/1.02  
% 2.77/1.02  fof(f38,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.77/1.02    inference(flattening,[],[f37])).
% 2.77/1.02  
% 2.77/1.02  fof(f70,plain,(
% 2.77/1.02    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f1,axiom,(
% 2.77/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f41,plain,(
% 2.77/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.77/1.02    inference(nnf_transformation,[],[f1])).
% 2.77/1.02  
% 2.77/1.02  fof(f42,plain,(
% 2.77/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.77/1.02    inference(rectify,[],[f41])).
% 2.77/1.02  
% 2.77/1.02  fof(f43,plain,(
% 2.77/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f44,plain,(
% 2.77/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.77/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.77/1.02  
% 2.77/1.02  fof(f51,plain,(
% 2.77/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f44])).
% 2.77/1.02  
% 2.77/1.02  fof(f6,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f25,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.77/1.02    inference(ennf_transformation,[],[f6])).
% 2.77/1.02  
% 2.77/1.02  fof(f56,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f25])).
% 2.77/1.02  
% 2.77/1.02  fof(f10,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f28,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(ennf_transformation,[],[f10])).
% 2.77/1.02  
% 2.77/1.02  fof(f60,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f28])).
% 2.77/1.02  
% 2.77/1.02  fof(f16,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f35,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.77/1.02    inference(ennf_transformation,[],[f16])).
% 2.77/1.02  
% 2.77/1.02  fof(f36,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.77/1.02    inference(flattening,[],[f35])).
% 2.77/1.02  
% 2.77/1.02  fof(f69,plain,(
% 2.77/1.02    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f36])).
% 2.77/1.02  
% 2.77/1.02  fof(f73,plain,(
% 2.77/1.02    v1_funct_2(sK3,sK1,sK2)),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f76,plain,(
% 2.77/1.02    v1_funct_2(sK4,sK2,sK1)),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f9,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f21,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.77/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.77/1.02  
% 2.77/1.02  fof(f27,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(ennf_transformation,[],[f21])).
% 2.77/1.02  
% 2.77/1.02  fof(f59,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f27])).
% 2.77/1.02  
% 2.77/1.02  fof(f12,axiom,(
% 2.77/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f31,plain,(
% 2.77/1.02    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.77/1.02    inference(ennf_transformation,[],[f12])).
% 2.77/1.02  
% 2.77/1.02  fof(f32,plain,(
% 2.77/1.02    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.77/1.02    inference(flattening,[],[f31])).
% 2.77/1.02  
% 2.77/1.02  fof(f46,plain,(
% 2.77/1.02    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.77/1.02    inference(nnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f64,plain,(
% 2.77/1.02    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f46])).
% 2.77/1.02  
% 2.77/1.02  fof(f82,plain,(
% 2.77/1.02    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.77/1.02    inference(equality_resolution,[],[f64])).
% 2.77/1.02  
% 2.77/1.02  fof(f8,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f26,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(ennf_transformation,[],[f8])).
% 2.77/1.02  
% 2.77/1.02  fof(f58,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f26])).
% 2.77/1.02  
% 2.77/1.02  fof(f79,plain,(
% 2.77/1.02    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 2.77/1.02    inference(cnf_transformation,[],[f49])).
% 2.77/1.02  
% 2.77/1.02  fof(f5,axiom,(
% 2.77/1.02    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f24,plain,(
% 2.77/1.02    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.77/1.02    inference(ennf_transformation,[],[f5])).
% 2.77/1.02  
% 2.77/1.02  fof(f55,plain,(
% 2.77/1.02    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f24])).
% 2.77/1.02  
% 2.77/1.02  fof(f3,axiom,(
% 2.77/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f22,plain,(
% 2.77/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.77/1.02    inference(ennf_transformation,[],[f3])).
% 2.77/1.02  
% 2.77/1.02  fof(f53,plain,(
% 2.77/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f22])).
% 2.77/1.02  
% 2.77/1.02  fof(f2,axiom,(
% 2.77/1.02    v1_xboole_0(k1_xboole_0)),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f52,plain,(
% 2.77/1.02    v1_xboole_0(k1_xboole_0)),
% 2.77/1.02    inference(cnf_transformation,[],[f2])).
% 2.77/1.02  
% 2.77/1.02  fof(f7,axiom,(
% 2.77/1.02    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f57,plain,(
% 2.77/1.02    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f7])).
% 2.77/1.02  
% 2.77/1.02  fof(f15,axiom,(
% 2.77/1.02    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f68,plain,(
% 2.77/1.02    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f15])).
% 2.77/1.02  
% 2.77/1.02  fof(f80,plain,(
% 2.77/1.02    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.77/1.02    inference(definition_unfolding,[],[f57,f68])).
% 2.77/1.02  
% 2.77/1.02  cnf(c_737,plain,
% 2.77/1.02      ( ~ v2_funct_1(X0_50) | v2_funct_1(X1_50) | X1_50 != X0_50 ),
% 2.77/1.02      theory(equality) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2735,plain,
% 2.77/1.02      ( ~ v2_funct_1(X0_50) | v2_funct_1(sK3) | sK3 != X0_50 ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_737]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2737,plain,
% 2.77/1.02      ( v2_funct_1(sK3) | ~ v2_funct_1(sK1) | sK3 != sK1 ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_2735]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_15,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.77/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.77/1.02      | ~ v1_funct_1(X0)
% 2.77/1.02      | ~ v1_funct_1(X3) ),
% 2.77/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_719,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.77/1.02      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 2.77/1.02      | m1_subset_1(k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 2.77/1.02      | ~ v1_funct_1(X0_50)
% 2.77/1.02      | ~ v1_funct_1(X3_50) ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1170,plain,
% 2.77/1.02      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 2.77/1.02      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50))) != iProver_top
% 2.77/1.02      | m1_subset_1(k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) = iProver_top
% 2.77/1.02      | v1_funct_1(X3_50) != iProver_top
% 2.77/1.02      | v1_funct_1(X0_50) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_12,plain,
% 2.77/1.02      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.77/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.77/1.02      | X3 = X2 ),
% 2.77/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_22,negated_conjecture,
% 2.77/1.02      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 2.77/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_482,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | X3 = X0
% 2.77/1.02      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 2.77/1.02      | k6_partfun1(sK1) != X3
% 2.77/1.02      | sK1 != X2
% 2.77/1.02      | sK1 != X1 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_483,plain,
% 2.77/1.02      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/1.02      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/1.02      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_482]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_17,plain,
% 2.77/1.02      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_47,plain,
% 2.77/1.02      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_485,plain,
% 2.77/1.02      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/1.02      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_483,c_47]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_705,plain,
% 2.77/1.02      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/1.02      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_485]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1185,plain,
% 2.77/1.02      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.77/1.02      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2143,plain,
% 2.77/1.02      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1)
% 2.77/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.77/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.77/1.02      | v1_funct_1(sK3) != iProver_top
% 2.77/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1170,c_1185]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_28,negated_conjecture,
% 2.77/1.02      ( v1_funct_1(sK3) ),
% 2.77/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_29,plain,
% 2.77/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_26,negated_conjecture,
% 2.77/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_31,plain,
% 2.77/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_25,negated_conjecture,
% 2.77/1.02      ( v1_funct_1(sK4) ),
% 2.77/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_32,plain,
% 2.77/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_23,negated_conjecture,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_34,plain,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2472,plain,
% 2.77/1.02      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_2143,c_29,c_31,c_32,c_34]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_20,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.02      | ~ v1_funct_2(X3,X4,X1)
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ v1_funct_1(X0)
% 2.77/1.02      | ~ v1_funct_1(X3)
% 2.77/1.02      | v2_funct_1(X3)
% 2.77/1.02      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.77/1.02      | k1_xboole_0 = X2 ),
% 2.77/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_715,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 2.77/1.02      | ~ v1_funct_2(X3_50,X4_50,X1_50)
% 2.77/1.02      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.77/1.02      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50)))
% 2.77/1.02      | ~ v1_funct_1(X0_50)
% 2.77/1.02      | ~ v1_funct_1(X3_50)
% 2.77/1.02      | v2_funct_1(X3_50)
% 2.77/1.02      | ~ v2_funct_1(k1_partfun1(X4_50,X1_50,X1_50,X2_50,X3_50,X0_50))
% 2.77/1.02      | k1_xboole_0 = X2_50 ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1174,plain,
% 2.77/1.02      ( k1_xboole_0 = X0_50
% 2.77/1.02      | v1_funct_2(X1_50,X2_50,X0_50) != iProver_top
% 2.77/1.02      | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
% 2.77/1.02      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X0_50))) != iProver_top
% 2.77/1.02      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
% 2.77/1.02      | v1_funct_1(X3_50) != iProver_top
% 2.77/1.02      | v1_funct_1(X1_50) != iProver_top
% 2.77/1.02      | v2_funct_1(X3_50) = iProver_top
% 2.77/1.02      | v2_funct_1(k1_partfun1(X4_50,X2_50,X2_50,X0_50,X3_50,X1_50)) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2498,plain,
% 2.77/1.02      ( sK1 = k1_xboole_0
% 2.77/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.77/1.02      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.77/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.77/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.77/1.02      | v1_funct_1(sK3) != iProver_top
% 2.77/1.02      | v1_funct_1(sK4) != iProver_top
% 2.77/1.02      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 2.77/1.02      | v2_funct_1(sK3) = iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_2472,c_1174]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_0,plain,
% 2.77/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_6,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/1.02      | ~ r2_hidden(X2,X0)
% 2.77/1.02      | ~ v1_xboole_0(X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_326,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/1.02      | ~ v1_xboole_0(X1)
% 2.77/1.02      | v1_xboole_0(X2)
% 2.77/1.02      | X0 != X2
% 2.77/1.02      | sK0(X2) != X3 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_327,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/1.02      | ~ v1_xboole_0(X1)
% 2.77/1.02      | v1_xboole_0(X0) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_326]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_708,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 2.77/1.02      | ~ v1_xboole_0(X1_50)
% 2.77/1.02      | v1_xboole_0(X0_50) ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_327]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1842,plain,
% 2.77/1.02      ( ~ m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(X1_50))
% 2.77/1.02      | ~ v1_xboole_0(X1_50)
% 2.77/1.02      | v1_xboole_0(k6_partfun1(X0_50)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_708]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2441,plain,
% 2.77/1.02      ( ~ m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.77/1.02      | ~ v1_xboole_0(k2_zfmisc_1(X1_50,X2_50))
% 2.77/1.02      | v1_xboole_0(k6_partfun1(X0_50)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1842]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2443,plain,
% 2.77/1.02      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.77/1.02      | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK1))
% 2.77/1.02      | v1_xboole_0(k6_partfun1(sK1)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_2441]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_714,negated_conjecture,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1175,plain,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_10,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_720,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 2.77/1.02      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1169,plain,
% 2.77/1.02      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 2.77/1.02      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2055,plain,
% 2.77/1.02      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1175,c_1169]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_18,plain,
% 2.77/1.02      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.77/1.02      | ~ v1_funct_2(X2,X0,X1)
% 2.77/1.02      | ~ v1_funct_2(X3,X1,X0)
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.77/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.77/1.02      | ~ v1_funct_1(X2)
% 2.77/1.02      | ~ v1_funct_1(X3)
% 2.77/1.02      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.77/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_496,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.02      | ~ v1_funct_2(X3,X2,X1)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.77/1.02      | ~ v1_funct_1(X3)
% 2.77/1.02      | ~ v1_funct_1(X0)
% 2.77/1.02      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.77/1.02      | k2_relset_1(X2,X1,X3) = X1
% 2.77/1.02      | k6_partfun1(X1) != k6_partfun1(sK1)
% 2.77/1.02      | sK1 != X1 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_497,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,sK1)
% 2.77/1.02      | ~ v1_funct_2(X2,sK1,X1)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.77/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.77/1.02      | ~ v1_funct_1(X2)
% 2.77/1.02      | ~ v1_funct_1(X0)
% 2.77/1.02      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.77/1.02      | k2_relset_1(X1,sK1,X0) = sK1
% 2.77/1.02      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_496]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_573,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,sK1)
% 2.77/1.02      | ~ v1_funct_2(X2,sK1,X1)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 2.77/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.77/1.02      | ~ v1_funct_1(X0)
% 2.77/1.02      | ~ v1_funct_1(X2)
% 2.77/1.02      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.77/1.02      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 2.77/1.02      inference(equality_resolution_simp,[status(thm)],[c_497]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_704,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0_50,X1_50,sK1)
% 2.77/1.02      | ~ v1_funct_2(X2_50,sK1,X1_50)
% 2.77/1.02      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1)))
% 2.77/1.02      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X1_50)))
% 2.77/1.02      | ~ v1_funct_1(X0_50)
% 2.77/1.02      | ~ v1_funct_1(X2_50)
% 2.77/1.02      | k1_partfun1(sK1,X1_50,X1_50,sK1,X2_50,X0_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.77/1.02      | k2_relset_1(X1_50,sK1,X0_50) = sK1 ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_573]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1186,plain,
% 2.77/1.02      ( k1_partfun1(sK1,X0_50,X0_50,sK1,X1_50,X2_50) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 2.77/1.02      | k2_relset_1(X0_50,sK1,X2_50) = sK1
% 2.77/1.02      | v1_funct_2(X2_50,X0_50,sK1) != iProver_top
% 2.77/1.02      | v1_funct_2(X1_50,sK1,X0_50) != iProver_top
% 2.77/1.02      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 2.77/1.02      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_50))) != iProver_top
% 2.77/1.02      | v1_funct_1(X2_50) != iProver_top
% 2.77/1.02      | v1_funct_1(X1_50) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1829,plain,
% 2.77/1.02      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 2.77/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.77/1.02      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 2.77/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.77/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 2.77/1.02      | v1_funct_1(sK3) != iProver_top
% 2.77/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.77/1.02      inference(equality_resolution,[status(thm)],[c_1186]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_27,negated_conjecture,
% 2.77/1.02      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.77/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_30,plain,
% 2.77/1.02      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_24,negated_conjecture,
% 2.77/1.02      ( v1_funct_2(sK4,sK2,sK1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_33,plain,
% 2.77/1.02      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1832,plain,
% 2.77/1.02      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_1829,c_29,c_30,c_31,c_32,c_33,c_34]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2068,plain,
% 2.77/1.02      ( k2_relat_1(sK4) = sK1 ),
% 2.77/1.02      inference(light_normalisation,[status(thm)],[c_2055,c_1832]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_9,plain,
% 2.77/1.02      ( v5_relat_1(X0,X1)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_13,plain,
% 2.77/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.77/1.02      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.77/1.02      | ~ v1_relat_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_400,plain,
% 2.77/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.77/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.77/1.02      | ~ v1_relat_1(X0)
% 2.77/1.02      | X0 != X1
% 2.77/1.02      | k2_relat_1(X0) != X3 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_401,plain,
% 2.77/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.77/1.02      | ~ v1_relat_1(X0) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_400]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_8,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | v1_relat_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_411,plain,
% 2.77/1.02      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.77/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_401,c_8]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_21,negated_conjecture,
% 2.77/1.02      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 2.77/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_426,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.77/1.02      | ~ v2_funct_1(sK3)
% 2.77/1.02      | k2_relat_1(X0) != sK1
% 2.77/1.02      | sK4 != X0 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_411,c_21]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_427,plain,
% 2.77/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 2.77/1.02      | ~ v2_funct_1(sK3)
% 2.77/1.02      | k2_relat_1(sK4) != sK1 ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_426]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_707,plain,
% 2.77/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
% 2.77/1.02      | ~ v2_funct_1(sK3)
% 2.77/1.02      | k2_relat_1(sK4) != sK1 ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_427]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_726,plain,
% 2.77/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4))))
% 2.77/1.02      | ~ sP0_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.77/1.02                [c_707]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1183,plain,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK4)))) != iProver_top
% 2.77/1.02      | sP0_iProver_split != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2326,plain,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 2.77/1.02      | sP0_iProver_split != iProver_top ),
% 2.77/1.02      inference(demodulation,[status(thm)],[c_2068,c_1183]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2384,plain,
% 2.77/1.02      ( sP0_iProver_split != iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1175,c_2326]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2390,plain,
% 2.77/1.02      ( ~ sP0_iProver_split ),
% 2.77/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2384]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_727,plain,
% 2.77/1.02      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[])],
% 2.77/1.02                [c_707]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1182,plain,
% 2.77/1.02      ( k2_relat_1(sK4) != sK1
% 2.77/1.02      | v2_funct_1(sK3) != iProver_top
% 2.77/1.02      | sP0_iProver_split = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2327,plain,
% 2.77/1.02      ( sK1 != sK1
% 2.77/1.02      | v2_funct_1(sK3) != iProver_top
% 2.77/1.02      | sP0_iProver_split = iProver_top ),
% 2.77/1.02      inference(demodulation,[status(thm)],[c_2068,c_1182]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2328,plain,
% 2.77/1.02      ( v2_funct_1(sK3) != iProver_top
% 2.77/1.02      | sP0_iProver_split = iProver_top ),
% 2.77/1.02      inference(equality_resolution_simp,[status(thm)],[c_2327]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_732,plain,
% 2.77/1.02      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(X1_50) | X1_50 != X0_50 ),
% 2.77/1.02      theory(equality) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2248,plain,
% 2.77/1.02      ( v1_xboole_0(X0_50)
% 2.77/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.77/1.02      | X0_50 != k1_xboole_0 ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_732]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2250,plain,
% 2.77/1.02      ( v1_xboole_0(sK1)
% 2.77/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.77/1.02      | sK1 != k1_xboole_0 ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_2248]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_5,plain,
% 2.77/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 2.77/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_722,plain,
% 2.77/1.02      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(k2_zfmisc_1(X0_50,X1_50)) ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2121,plain,
% 2.77/1.02      ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~ v1_xboole_0(sK1) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_722]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1734,plain,
% 2.77/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_50))
% 2.77/1.02      | ~ v1_xboole_0(X0_50)
% 2.77/1.02      | v1_xboole_0(sK3) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_708]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2019,plain,
% 2.77/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.77/1.02      | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
% 2.77/1.02      | v1_xboole_0(sK3) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1734]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3,plain,
% 2.77/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.77/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_724,plain,
% 2.77/1.02      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(X1_50) | X1_50 = X0_50 ),
% 2.77/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1779,plain,
% 2.77/1.02      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(sK3) | sK3 = X0_50 ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_724]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1781,plain,
% 2.77/1.02      ( ~ v1_xboole_0(sK3) | ~ v1_xboole_0(sK1) | sK3 = sK1 ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1779]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1604,plain,
% 2.77/1.02      ( ~ v1_xboole_0(X0_50)
% 2.77/1.02      | ~ v1_xboole_0(k6_partfun1(X1_50))
% 2.77/1.02      | X0_50 = k6_partfun1(X1_50) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_724]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1606,plain,
% 2.77/1.02      ( ~ v1_xboole_0(k6_partfun1(sK1))
% 2.77/1.02      | ~ v1_xboole_0(sK1)
% 2.77/1.02      | sK1 = k6_partfun1(sK1) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1604]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1394,plain,
% 2.77/1.02      ( v2_funct_1(X0_50)
% 2.77/1.02      | ~ v2_funct_1(k6_partfun1(X1_50))
% 2.77/1.02      | X0_50 != k6_partfun1(X1_50) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_737]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1396,plain,
% 2.77/1.02      ( ~ v2_funct_1(k6_partfun1(sK1))
% 2.77/1.02      | v2_funct_1(sK1)
% 2.77/1.02      | sK1 != k6_partfun1(sK1) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1394]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2,plain,
% 2.77/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_83,plain,
% 2.77/1.02      ( v1_xboole_0(k2_zfmisc_1(sK1,sK1)) | ~ v1_xboole_0(sK1) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_7,plain,
% 2.77/1.02      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.77/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_76,plain,
% 2.77/1.02      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_78,plain,
% 2.77/1.02      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_76]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_77,plain,
% 2.77/1.02      ( v2_funct_1(k6_partfun1(sK1)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(contradiction,plain,
% 2.77/1.02      ( $false ),
% 2.77/1.02      inference(minisat,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_2737,c_2498,c_2443,c_2390,c_2384,c_2328,c_2250,c_2121,
% 2.77/1.02                 c_2068,c_2019,c_1781,c_1606,c_1396,c_727,c_2,c_83,c_78,
% 2.77/1.02                 c_77,c_47,c_34,c_33,c_32,c_31,c_26,c_30,c_29]) ).
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  ------                               Statistics
% 2.77/1.02  
% 2.77/1.02  ------ General
% 2.77/1.02  
% 2.77/1.02  abstr_ref_over_cycles:                  0
% 2.77/1.02  abstr_ref_under_cycles:                 0
% 2.77/1.02  gc_basic_clause_elim:                   0
% 2.77/1.02  forced_gc_time:                         0
% 2.77/1.02  parsing_time:                           0.007
% 2.77/1.02  unif_index_cands_time:                  0.
% 2.77/1.02  unif_index_add_time:                    0.
% 2.77/1.02  orderings_time:                         0.
% 2.77/1.02  out_proof_time:                         0.015
% 2.77/1.02  total_time:                             0.103
% 2.77/1.02  num_of_symbols:                         56
% 2.77/1.02  num_of_terms:                           3451
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing
% 2.77/1.02  
% 2.77/1.02  num_of_splits:                          1
% 2.77/1.02  num_of_split_atoms:                     1
% 2.77/1.02  num_of_reused_defs:                     0
% 2.77/1.02  num_eq_ax_congr_red:                    12
% 2.77/1.02  num_of_sem_filtered_clauses:            1
% 2.77/1.02  num_of_subtypes:                        2
% 2.77/1.02  monotx_restored_types:                  1
% 2.77/1.02  sat_num_of_epr_types:                   0
% 2.77/1.02  sat_num_of_non_cyclic_types:            0
% 2.77/1.02  sat_guarded_non_collapsed_types:        1
% 2.77/1.02  num_pure_diseq_elim:                    0
% 2.77/1.02  simp_replaced_by:                       0
% 2.77/1.02  res_preprocessed:                       126
% 2.77/1.02  prep_upred:                             0
% 2.77/1.02  prep_unflattend:                        21
% 2.77/1.02  smt_new_axioms:                         0
% 2.77/1.02  pred_elim_cands:                        5
% 2.77/1.02  pred_elim:                              5
% 2.77/1.02  pred_elim_cl:                           7
% 2.77/1.02  pred_elim_cycles:                       8
% 2.77/1.02  merged_defs:                            0
% 2.77/1.02  merged_defs_ncl:                        0
% 2.77/1.02  bin_hyper_res:                          0
% 2.77/1.02  prep_cycles:                            4
% 2.77/1.02  pred_elim_time:                         0.004
% 2.77/1.02  splitting_time:                         0.
% 2.77/1.02  sem_filter_time:                        0.
% 2.77/1.02  monotx_time:                            0.
% 2.77/1.02  subtype_inf_time:                       0.001
% 2.77/1.02  
% 2.77/1.02  ------ Problem properties
% 2.77/1.02  
% 2.77/1.02  clauses:                                23
% 2.77/1.02  conjectures:                            6
% 2.77/1.02  epr:                                    6
% 2.77/1.02  horn:                                   22
% 2.77/1.02  ground:                                 9
% 2.77/1.02  unary:                                  9
% 2.77/1.02  binary:                                 5
% 2.77/1.02  lits:                                   71
% 2.77/1.02  lits_eq:                                9
% 2.77/1.02  fd_pure:                                0
% 2.77/1.02  fd_pseudo:                              0
% 2.77/1.02  fd_cond:                                1
% 2.77/1.02  fd_pseudo_cond:                         1
% 2.77/1.02  ac_symbols:                             0
% 2.77/1.02  
% 2.77/1.02  ------ Propositional Solver
% 2.77/1.02  
% 2.77/1.02  prop_solver_calls:                      27
% 2.77/1.02  prop_fast_solver_calls:                 909
% 2.77/1.02  smt_solver_calls:                       0
% 2.77/1.02  smt_fast_solver_calls:                  0
% 2.77/1.02  prop_num_of_clauses:                    925
% 2.77/1.02  prop_preprocess_simplified:             3959
% 2.77/1.02  prop_fo_subsumed:                       16
% 2.77/1.02  prop_solver_time:                       0.
% 2.77/1.02  smt_solver_time:                        0.
% 2.77/1.02  smt_fast_solver_time:                   0.
% 2.77/1.02  prop_fast_solver_time:                  0.
% 2.77/1.02  prop_unsat_core_time:                   0.
% 2.77/1.02  
% 2.77/1.02  ------ QBF
% 2.77/1.02  
% 2.77/1.02  qbf_q_res:                              0
% 2.77/1.02  qbf_num_tautologies:                    0
% 2.77/1.02  qbf_prep_cycles:                        0
% 2.77/1.02  
% 2.77/1.02  ------ BMC1
% 2.77/1.02  
% 2.77/1.02  bmc1_current_bound:                     -1
% 2.77/1.02  bmc1_last_solved_bound:                 -1
% 2.77/1.02  bmc1_unsat_core_size:                   -1
% 2.77/1.02  bmc1_unsat_core_parents_size:           -1
% 2.77/1.02  bmc1_merge_next_fun:                    0
% 2.77/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.02  
% 2.77/1.02  ------ Instantiation
% 2.77/1.02  
% 2.77/1.02  inst_num_of_clauses:                    241
% 2.77/1.02  inst_num_in_passive:                    73
% 2.77/1.02  inst_num_in_active:                     146
% 2.77/1.02  inst_num_in_unprocessed:                21
% 2.77/1.02  inst_num_of_loops:                      191
% 2.77/1.02  inst_num_of_learning_restarts:          0
% 2.77/1.02  inst_num_moves_active_passive:          41
% 2.77/1.02  inst_lit_activity:                      0
% 2.77/1.02  inst_lit_activity_moves:                0
% 2.77/1.02  inst_num_tautologies:                   0
% 2.77/1.02  inst_num_prop_implied:                  0
% 2.77/1.02  inst_num_existing_simplified:           0
% 2.77/1.02  inst_num_eq_res_simplified:             0
% 2.77/1.02  inst_num_child_elim:                    0
% 2.77/1.02  inst_num_of_dismatching_blockings:      8
% 2.77/1.02  inst_num_of_non_proper_insts:           220
% 2.77/1.02  inst_num_of_duplicates:                 0
% 2.77/1.02  inst_inst_num_from_inst_to_res:         0
% 2.77/1.02  inst_dismatching_checking_time:         0.
% 2.77/1.02  
% 2.77/1.02  ------ Resolution
% 2.77/1.02  
% 2.77/1.02  res_num_of_clauses:                     0
% 2.77/1.02  res_num_in_passive:                     0
% 2.77/1.02  res_num_in_active:                      0
% 2.77/1.02  res_num_of_loops:                       130
% 2.77/1.02  res_forward_subset_subsumed:            17
% 2.77/1.02  res_backward_subset_subsumed:           0
% 2.77/1.02  res_forward_subsumed:                   0
% 2.77/1.02  res_backward_subsumed:                  0
% 2.77/1.02  res_forward_subsumption_resolution:     3
% 2.77/1.02  res_backward_subsumption_resolution:    0
% 2.77/1.02  res_clause_to_clause_subsumption:       106
% 2.77/1.02  res_orphan_elimination:                 0
% 2.77/1.02  res_tautology_del:                      19
% 2.77/1.02  res_num_eq_res_simplified:              1
% 2.77/1.02  res_num_sel_changes:                    0
% 2.77/1.02  res_moves_from_active_to_pass:          0
% 2.77/1.02  
% 2.77/1.02  ------ Superposition
% 2.77/1.02  
% 2.77/1.02  sup_time_total:                         0.
% 2.77/1.02  sup_time_generating:                    0.
% 2.77/1.02  sup_time_sim_full:                      0.
% 2.77/1.02  sup_time_sim_immed:                     0.
% 2.77/1.02  
% 2.77/1.02  sup_num_of_clauses:                     50
% 2.77/1.02  sup_num_in_active:                      33
% 2.77/1.02  sup_num_in_passive:                     17
% 2.77/1.02  sup_num_of_loops:                       38
% 2.77/1.02  sup_fw_superposition:                   24
% 2.77/1.02  sup_bw_superposition:                   10
% 2.77/1.02  sup_immediate_simplified:               4
% 2.77/1.02  sup_given_eliminated:                   1
% 2.77/1.02  comparisons_done:                       0
% 2.77/1.02  comparisons_avoided:                    0
% 2.77/1.02  
% 2.77/1.02  ------ Simplifications
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  sim_fw_subset_subsumed:                 1
% 2.77/1.02  sim_bw_subset_subsumed:                 0
% 2.77/1.02  sim_fw_subsumed:                        1
% 2.77/1.02  sim_bw_subsumed:                        1
% 2.77/1.02  sim_fw_subsumption_res:                 0
% 2.77/1.02  sim_bw_subsumption_res:                 0
% 2.77/1.02  sim_tautology_del:                      1
% 2.77/1.02  sim_eq_tautology_del:                   2
% 2.77/1.02  sim_eq_res_simp:                        1
% 2.77/1.02  sim_fw_demodulated:                     2
% 2.77/1.02  sim_bw_demodulated:                     4
% 2.77/1.02  sim_light_normalised:                   1
% 2.77/1.02  sim_joinable_taut:                      0
% 2.77/1.02  sim_joinable_simp:                      0
% 2.77/1.02  sim_ac_normalised:                      0
% 2.77/1.02  sim_smt_subsumption:                    0
% 2.77/1.02  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:08 EST 2020

% Result     : Theorem 11.84s
% Output     : CNFRefutation 11.84s
% Verified   : 
% Statistics : Number of formulae       :  233 ( 735 expanded)
%              Number of clauses        :  134 ( 224 expanded)
%              Number of leaves         :   30 ( 181 expanded)
%              Depth                    :   17
%              Number of atoms          :  716 (4142 expanded)
%              Number of equality atoms :  164 ( 277 expanded)
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
    inference(cnf_transformation,[],[f44])).

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

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

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

fof(f102,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f106,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f83,f93])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f104,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f93])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

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

fof(f77,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f88,plain,(
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
    inference(equality_resolution,[],[f88])).

fof(f103,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f72,plain,(
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

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f100,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_750,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_41918,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_41920,plain,
    ( v2_funct_1(sK4)
    | ~ v2_funct_1(sK2)
    | sK4 != sK2 ),
    inference(instantiation,[status(thm)],[c_41918])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22141,plain,
    ( ~ r2_hidden(sK1(X0,k6_partfun1(X1)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_22143,plain,
    ( ~ r2_hidden(sK1(sK2,k6_partfun1(sK2)),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_22141])).

cnf(c_22127,plain,
    ( ~ r2_hidden(sK1(X0,sK4),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_22129,plain,
    ( ~ r2_hidden(sK1(sK2,sK4),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_22127])).

cnf(c_742,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_14243,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_14245,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_14243])).

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

cnf(c_739,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_738,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3763,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_739,c_738])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
    | k6_partfun1(sK2) != X3
    | sK2 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_437,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_28,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_58,plain,
    ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_439,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_58])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2030,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_2758,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_4296,plain,
    ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2758])).

cnf(c_6852,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_39,c_37,c_36,c_34,c_58,c_437,c_4296])).

cnf(c_7807,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
    inference(resolution,[status(thm)],[c_3763,c_6852])).

cnf(c_8672,plain,
    ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
    | ~ v2_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[status(thm)],[c_7807,c_750])).

cnf(c_19,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_11836,plain,
    ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8672,c_85])).

cnf(c_12385,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | v2_funct_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_31,c_11836])).

cnf(c_10536,plain,
    ( ~ r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0))
    | ~ v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10538,plain,
    ( ~ r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2))
    | ~ v1_xboole_0(k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_10536])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1368,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1359,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3005,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1367])).

cnf(c_5959,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_3005])).

cnf(c_5960,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5959])).

cnf(c_5962,plain,
    ( v1_xboole_0(k6_partfun1(sK2))
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5960])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5896,plain,
    ( r1_tarski(X0,k6_partfun1(X1))
    | r2_hidden(sK1(X0,k6_partfun1(X1)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5898,plain,
    ( r1_tarski(sK2,k6_partfun1(sK2))
    | r2_hidden(sK1(sK2,k6_partfun1(sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_5896])).

cnf(c_1352,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1355,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1358,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4651,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1358])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5015,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4651,c_43])).

cnf(c_5016,plain,
    ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5015])).

cnf(c_5027,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_5016])).

cnf(c_1739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2010,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_2693,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_4284,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2693])).

cnf(c_5225,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5027,c_39,c_37,c_36,c_34,c_4284])).

cnf(c_1348,plain,
    ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
    | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_5228,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
    | m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5225,c_1348])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1361,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5230,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5225,c_1361])).

cnf(c_5724,plain,
    ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5228,c_40,c_42,c_43,c_45,c_5230])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1364,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5728,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5724,c_1364])).

cnf(c_17,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5729,plain,
    ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5728,c_17])).

cnf(c_5454,plain,
    ( ~ r2_hidden(sK1(sK4,X0),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5456,plain,
    ( ~ r2_hidden(sK1(sK4,sK2),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5454])).

cnf(c_3404,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3406,plain,
    ( r1_tarski(sK2,sK4)
    | r2_hidden(sK1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_3404])).

cnf(c_3337,plain,
    ( r1_tarski(k6_partfun1(X0),X1)
    | r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3339,plain,
    ( r1_tarski(k6_partfun1(sK2),sK2)
    | r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3337])).

cnf(c_3007,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1352,c_1367])).

cnf(c_3279,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_3007])).

cnf(c_3280,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3279])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_14])).

cnf(c_1347,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_2774,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1347])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2103,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK2))
    | v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_12,c_34])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2110,plain,
    ( v1_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2103,c_15])).

cnf(c_2111,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_3050,plain,
    ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2774,c_2111])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1370,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3055,plain,
    ( k2_relat_1(sK5) = sK2
    | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3050,c_1370])).

cnf(c_2446,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2448,plain,
    ( ~ r1_tarski(sK4,sK2)
    | ~ r1_tarski(sK2,sK4)
    | sK4 = sK2 ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_2426,plain,
    ( r1_tarski(sK4,X0)
    | r2_hidden(sK1(sK4,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2428,plain,
    ( r1_tarski(sK4,sK2)
    | r2_hidden(sK1(sK4,sK2),sK4) ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_32,negated_conjecture,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_455,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_456,plain,
    ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_509,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) != sK2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_456])).

cnf(c_510,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_520,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_510,c_6])).

cnf(c_2362,plain,
    ( ~ v2_funct_1(sK4)
    | k2_relat_1(sK5) != sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2110,c_520])).

cnf(c_2105,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_12,c_37])).

cnf(c_2117,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2105,c_15])).

cnf(c_2118,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2117])).

cnf(c_1869,plain,
    ( ~ r1_tarski(X0,k6_partfun1(X1))
    | ~ r1_tarski(k6_partfun1(X1),X0)
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1871,plain,
    ( ~ r1_tarski(k6_partfun1(sK2),sK2)
    | ~ r1_tarski(sK2,k6_partfun1(sK2))
    | sK2 = k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_1642,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1644,plain,
    ( ~ v2_funct_1(k6_partfun1(sK2))
    | v2_funct_1(sK2)
    | sK2 != k6_partfun1(sK2) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_419,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_420,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_422,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_117,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_113,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41920,c_22143,c_22129,c_14245,c_12385,c_10538,c_5962,c_5898,c_5729,c_5456,c_3406,c_3339,c_3280,c_3055,c_2448,c_2428,c_2362,c_2118,c_2111,c_1871,c_1644,c_422,c_117,c_113,c_85,c_34,c_35,c_36,c_37,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.84/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.84/1.99  
% 11.84/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.84/1.99  
% 11.84/1.99  ------  iProver source info
% 11.84/1.99  
% 11.84/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.84/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.84/1.99  git: non_committed_changes: false
% 11.84/1.99  git: last_make_outside_of_git: false
% 11.84/1.99  
% 11.84/1.99  ------ 
% 11.84/1.99  ------ Parsing...
% 11.84/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.84/1.99  
% 11.84/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.84/1.99  
% 11.84/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.84/1.99  
% 11.84/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.84/1.99  ------ Proving...
% 11.84/1.99  ------ Problem Properties 
% 11.84/1.99  
% 11.84/1.99  
% 11.84/1.99  clauses                                 32
% 11.84/1.99  conjectures                             6
% 11.84/1.99  EPR                                     9
% 11.84/1.99  Horn                                    29
% 11.84/1.99  unary                                   13
% 11.84/1.99  binary                                  7
% 11.84/1.99  lits                                    80
% 11.84/1.99  lits eq                                 7
% 11.84/1.99  fd_pure                                 0
% 11.84/1.99  fd_pseudo                               0
% 11.84/1.99  fd_cond                                 1
% 11.84/1.99  fd_pseudo_cond                          1
% 11.84/1.99  AC symbols                              0
% 11.84/1.99  
% 11.84/1.99  ------ Input Options Time Limit: Unbounded
% 11.84/1.99  
% 11.84/1.99  
% 11.84/1.99  ------ 
% 11.84/1.99  Current options:
% 11.84/1.99  ------ 
% 11.84/1.99  
% 11.84/1.99  
% 11.84/1.99  
% 11.84/1.99  
% 11.84/1.99  ------ Proving...
% 11.84/1.99  
% 11.84/1.99  
% 11.84/1.99  % SZS status Theorem for theBenchmark.p
% 11.84/1.99  
% 11.84/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.84/1.99  
% 11.84/1.99  fof(f1,axiom,(
% 11.84/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f47,plain,(
% 11.84/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.84/1.99    inference(nnf_transformation,[],[f1])).
% 11.84/1.99  
% 11.84/1.99  fof(f48,plain,(
% 11.84/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.84/1.99    inference(rectify,[],[f47])).
% 11.84/1.99  
% 11.84/1.99  fof(f49,plain,(
% 11.84/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.84/1.99    introduced(choice_axiom,[])).
% 11.84/1.99  
% 11.84/1.99  fof(f50,plain,(
% 11.84/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.84/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 11.84/1.99  
% 11.84/1.99  fof(f63,plain,(
% 11.84/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f50])).
% 11.84/1.99  
% 11.84/1.99  fof(f21,axiom,(
% 11.84/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f43,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.84/1.99    inference(ennf_transformation,[],[f21])).
% 11.84/1.99  
% 11.84/1.99  fof(f44,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.84/1.99    inference(flattening,[],[f43])).
% 11.84/1.99  
% 11.84/1.99  fof(f94,plain,(
% 11.84/1.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f44])).
% 11.84/1.99  
% 11.84/1.99  fof(f15,axiom,(
% 11.84/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f35,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.84/1.99    inference(ennf_transformation,[],[f15])).
% 11.84/1.99  
% 11.84/1.99  fof(f36,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.84/1.99    inference(flattening,[],[f35])).
% 11.84/1.99  
% 11.84/1.99  fof(f58,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.84/1.99    inference(nnf_transformation,[],[f36])).
% 11.84/1.99  
% 11.84/1.99  fof(f85,plain,(
% 11.84/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.84/1.99    inference(cnf_transformation,[],[f58])).
% 11.84/1.99  
% 11.84/1.99  fof(f22,conjecture,(
% 11.84/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f23,negated_conjecture,(
% 11.84/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 11.84/1.99    inference(negated_conjecture,[],[f22])).
% 11.84/1.99  
% 11.84/1.99  fof(f45,plain,(
% 11.84/1.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.84/1.99    inference(ennf_transformation,[],[f23])).
% 11.84/1.99  
% 11.84/1.99  fof(f46,plain,(
% 11.84/1.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.84/1.99    inference(flattening,[],[f45])).
% 11.84/1.99  
% 11.84/1.99  fof(f61,plain,(
% 11.84/1.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK5),k6_partfun1(X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK5,X1,X0) & v1_funct_1(sK5))) )),
% 11.84/1.99    introduced(choice_axiom,[])).
% 11.84/1.99  
% 11.84/1.99  fof(f60,plain,(
% 11.84/1.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 11.84/1.99    introduced(choice_axiom,[])).
% 11.84/1.99  
% 11.84/1.99  fof(f62,plain,(
% 11.84/1.99    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 11.84/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f46,f61,f60])).
% 11.84/1.99  
% 11.84/1.99  fof(f102,plain,(
% 11.84/1.99    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  fof(f18,axiom,(
% 11.84/1.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f24,plain,(
% 11.84/1.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.84/1.99    inference(pure_predicate_removal,[],[f18])).
% 11.84/1.99  
% 11.84/1.99  fof(f91,plain,(
% 11.84/1.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.84/1.99    inference(cnf_transformation,[],[f24])).
% 11.84/1.99  
% 11.84/1.99  fof(f96,plain,(
% 11.84/1.99    v1_funct_1(sK4)),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  fof(f98,plain,(
% 11.84/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  fof(f99,plain,(
% 11.84/1.99    v1_funct_1(sK5)),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  fof(f101,plain,(
% 11.84/1.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  fof(f17,axiom,(
% 11.84/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f39,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.84/1.99    inference(ennf_transformation,[],[f17])).
% 11.84/1.99  
% 11.84/1.99  fof(f40,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.84/1.99    inference(flattening,[],[f39])).
% 11.84/1.99  
% 11.84/1.99  fof(f90,plain,(
% 11.84/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f40])).
% 11.84/1.99  
% 11.84/1.99  fof(f13,axiom,(
% 11.84/1.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f83,plain,(
% 11.84/1.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.84/1.99    inference(cnf_transformation,[],[f13])).
% 11.84/1.99  
% 11.84/1.99  fof(f20,axiom,(
% 11.84/1.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f93,plain,(
% 11.84/1.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f20])).
% 11.84/1.99  
% 11.84/1.99  fof(f106,plain,(
% 11.84/1.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.84/1.99    inference(definition_unfolding,[],[f83,f93])).
% 11.84/1.99  
% 11.84/1.99  fof(f6,axiom,(
% 11.84/1.99    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f29,plain,(
% 11.84/1.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 11.84/1.99    inference(ennf_transformation,[],[f6])).
% 11.84/1.99  
% 11.84/1.99  fof(f73,plain,(
% 11.84/1.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f29])).
% 11.84/1.99  
% 11.84/1.99  fof(f7,axiom,(
% 11.84/1.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f30,plain,(
% 11.84/1.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.84/1.99    inference(ennf_transformation,[],[f7])).
% 11.84/1.99  
% 11.84/1.99  fof(f74,plain,(
% 11.84/1.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f30])).
% 11.84/1.99  
% 11.84/1.99  fof(f2,axiom,(
% 11.84/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f26,plain,(
% 11.84/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.84/1.99    inference(ennf_transformation,[],[f2])).
% 11.84/1.99  
% 11.84/1.99  fof(f51,plain,(
% 11.84/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.84/1.99    inference(nnf_transformation,[],[f26])).
% 11.84/1.99  
% 11.84/1.99  fof(f52,plain,(
% 11.84/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.84/1.99    inference(rectify,[],[f51])).
% 11.84/1.99  
% 11.84/1.99  fof(f53,plain,(
% 11.84/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.84/1.99    introduced(choice_axiom,[])).
% 11.84/1.99  
% 11.84/1.99  fof(f54,plain,(
% 11.84/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.84/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 11.84/1.99  
% 11.84/1.99  fof(f66,plain,(
% 11.84/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f54])).
% 11.84/1.99  
% 11.84/1.99  fof(f19,axiom,(
% 11.84/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f41,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.84/1.99    inference(ennf_transformation,[],[f19])).
% 11.84/1.99  
% 11.84/1.99  fof(f42,plain,(
% 11.84/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.84/1.99    inference(flattening,[],[f41])).
% 11.84/1.99  
% 11.84/1.99  fof(f92,plain,(
% 11.84/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f42])).
% 11.84/1.99  
% 11.84/1.99  fof(f11,axiom,(
% 11.84/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f33,plain,(
% 11.84/1.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.84/1.99    inference(ennf_transformation,[],[f11])).
% 11.84/1.99  
% 11.84/1.99  fof(f79,plain,(
% 11.84/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f33])).
% 11.84/1.99  
% 11.84/1.99  fof(f12,axiom,(
% 11.84/1.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f81,plain,(
% 11.84/1.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.84/1.99    inference(cnf_transformation,[],[f12])).
% 11.84/1.99  
% 11.84/1.99  fof(f104,plain,(
% 11.84/1.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 11.84/1.99    inference(definition_unfolding,[],[f81,f93])).
% 11.84/1.99  
% 11.84/1.99  fof(f14,axiom,(
% 11.84/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f25,plain,(
% 11.84/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.84/1.99    inference(pure_predicate_removal,[],[f14])).
% 11.84/1.99  
% 11.84/1.99  fof(f34,plain,(
% 11.84/1.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.84/1.99    inference(ennf_transformation,[],[f25])).
% 11.84/1.99  
% 11.84/1.99  fof(f84,plain,(
% 11.84/1.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.84/1.99    inference(cnf_transformation,[],[f34])).
% 11.84/1.99  
% 11.84/1.99  fof(f9,axiom,(
% 11.84/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f32,plain,(
% 11.84/1.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.84/1.99    inference(ennf_transformation,[],[f9])).
% 11.84/1.99  
% 11.84/1.99  fof(f57,plain,(
% 11.84/1.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.84/1.99    inference(nnf_transformation,[],[f32])).
% 11.84/1.99  
% 11.84/1.99  fof(f76,plain,(
% 11.84/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f57])).
% 11.84/1.99  
% 11.84/1.99  fof(f8,axiom,(
% 11.84/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f31,plain,(
% 11.84/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.84/1.99    inference(ennf_transformation,[],[f8])).
% 11.84/1.99  
% 11.84/1.99  fof(f75,plain,(
% 11.84/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f31])).
% 11.84/1.99  
% 11.84/1.99  fof(f10,axiom,(
% 11.84/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f78,plain,(
% 11.84/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.84/1.99    inference(cnf_transformation,[],[f10])).
% 11.84/1.99  
% 11.84/1.99  fof(f3,axiom,(
% 11.84/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f55,plain,(
% 11.84/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.84/1.99    inference(nnf_transformation,[],[f3])).
% 11.84/1.99  
% 11.84/1.99  fof(f56,plain,(
% 11.84/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.84/1.99    inference(flattening,[],[f55])).
% 11.84/1.99  
% 11.84/1.99  fof(f70,plain,(
% 11.84/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f56])).
% 11.84/1.99  
% 11.84/1.99  fof(f77,plain,(
% 11.84/1.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f57])).
% 11.84/1.99  
% 11.84/1.99  fof(f16,axiom,(
% 11.84/1.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f37,plain,(
% 11.84/1.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.84/1.99    inference(ennf_transformation,[],[f16])).
% 11.84/1.99  
% 11.84/1.99  fof(f38,plain,(
% 11.84/1.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.84/1.99    inference(flattening,[],[f37])).
% 11.84/1.99  
% 11.84/1.99  fof(f59,plain,(
% 11.84/1.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.84/1.99    inference(nnf_transformation,[],[f38])).
% 11.84/1.99  
% 11.84/1.99  fof(f88,plain,(
% 11.84/1.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f59])).
% 11.84/1.99  
% 11.84/1.99  fof(f111,plain,(
% 11.84/1.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.84/1.99    inference(equality_resolution,[],[f88])).
% 11.84/1.99  
% 11.84/1.99  fof(f103,plain,(
% 11.84/1.99    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  fof(f69,plain,(
% 11.84/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.84/1.99    inference(cnf_transformation,[],[f56])).
% 11.84/1.99  
% 11.84/1.99  fof(f108,plain,(
% 11.84/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.84/1.99    inference(equality_resolution,[],[f69])).
% 11.84/1.99  
% 11.84/1.99  fof(f4,axiom,(
% 11.84/1.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f71,plain,(
% 11.84/1.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f4])).
% 11.84/1.99  
% 11.84/1.99  fof(f5,axiom,(
% 11.84/1.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 11.84/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.84/1.99  
% 11.84/1.99  fof(f27,plain,(
% 11.84/1.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 11.84/1.99    inference(ennf_transformation,[],[f5])).
% 11.84/1.99  
% 11.84/1.99  fof(f28,plain,(
% 11.84/1.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 11.84/1.99    inference(flattening,[],[f27])).
% 11.84/1.99  
% 11.84/1.99  fof(f72,plain,(
% 11.84/1.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 11.84/1.99    inference(cnf_transformation,[],[f28])).
% 11.84/1.99  
% 11.84/1.99  fof(f68,plain,(
% 11.84/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.84/1.99    inference(cnf_transformation,[],[f56])).
% 11.84/1.99  
% 11.84/1.99  fof(f109,plain,(
% 11.84/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.84/1.99    inference(equality_resolution,[],[f68])).
% 11.84/1.99  
% 11.84/1.99  fof(f100,plain,(
% 11.84/1.99    v1_funct_2(sK5,sK3,sK2)),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  fof(f97,plain,(
% 11.84/1.99    v1_funct_2(sK4,sK2,sK3)),
% 11.84/1.99    inference(cnf_transformation,[],[f62])).
% 11.84/1.99  
% 11.84/1.99  cnf(c_750,plain,
% 11.84/1.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 11.84/1.99      theory(equality) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_41918,plain,
% 11.84/1.99      ( ~ v2_funct_1(X0) | v2_funct_1(sK4) | sK4 != X0 ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_750]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_41920,plain,
% 11.84/1.99      ( v2_funct_1(sK4) | ~ v2_funct_1(sK2) | sK4 != sK2 ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_41918]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1,plain,
% 11.84/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.84/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_22141,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(X0,k6_partfun1(X1)),X0) | ~ v1_xboole_0(X0) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_22143,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(sK2,k6_partfun1(sK2)),sK2) | ~ v1_xboole_0(sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_22141]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_22127,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(X0,sK4),X0) | ~ v1_xboole_0(X0) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_22129,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(sK2,sK4),sK2) | ~ v1_xboole_0(sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_22127]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_742,plain,
% 11.84/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.84/1.99      theory(equality) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_14243,plain,
% 11.84/1.99      ( ~ r1_tarski(X0,X1)
% 11.84/1.99      | r1_tarski(X2,k1_xboole_0)
% 11.84/1.99      | X2 != X0
% 11.84/1.99      | k1_xboole_0 != X1 ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_742]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_14245,plain,
% 11.84/1.99      ( ~ r1_tarski(sK2,sK2)
% 11.84/1.99      | r1_tarski(sK2,k1_xboole_0)
% 11.84/1.99      | sK2 != sK2
% 11.84/1.99      | k1_xboole_0 != sK2 ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_14243]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_31,plain,
% 11.84/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.84/1.99      | ~ v1_funct_2(X3,X4,X1)
% 11.84/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.84/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | ~ v1_funct_1(X0)
% 11.84/1.99      | ~ v1_funct_1(X3)
% 11.84/1.99      | v2_funct_1(X3)
% 11.84/1.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.84/1.99      | k1_xboole_0 = X2 ),
% 11.84/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_739,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_738,plain,( X0 = X0 ),theory(equality) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3763,plain,
% 11.84/1.99      ( X0 != X1 | X1 = X0 ),
% 11.84/1.99      inference(resolution,[status(thm)],[c_739,c_738]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_23,plain,
% 11.84/1.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.84/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.84/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.84/1.99      | X3 = X2 ),
% 11.84/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_33,negated_conjecture,
% 11.84/1.99      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
% 11.84/1.99      inference(cnf_transformation,[],[f102]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_436,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | X3 = X0
% 11.84/1.99      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) != X0
% 11.84/1.99      | k6_partfun1(sK2) != X3
% 11.84/1.99      | sK2 != X2
% 11.84/1.99      | sK2 != X1 ),
% 11.84/1.99      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_437,plain,
% 11.84/1.99      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.84/1.99      | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.84/1.99      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 11.84/1.99      inference(unflattening,[status(thm)],[c_436]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_28,plain,
% 11.84/1.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.84/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_58,plain,
% 11.84/1.99      ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_28]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_439,plain,
% 11.84/1.99      ( ~ m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.84/1.99      | k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 11.84/1.99      inference(global_propositional_subsumption,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_437,c_58]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_39,negated_conjecture,
% 11.84/1.99      ( v1_funct_1(sK4) ),
% 11.84/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_37,negated_conjecture,
% 11.84/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 11.84/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_36,negated_conjecture,
% 11.84/1.99      ( v1_funct_1(sK5) ),
% 11.84/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_34,negated_conjecture,
% 11.84/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 11.84/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_26,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.84/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.84/1.99      | ~ v1_funct_1(X0)
% 11.84/1.99      | ~ v1_funct_1(X3) ),
% 11.84/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1729,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | m1_subset_1(k1_partfun1(X3,X4,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.84/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.84/1.99      | ~ v1_funct_1(X0)
% 11.84/1.99      | ~ v1_funct_1(sK4) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_26]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2030,plain,
% 11.84/1.99      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 11.84/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.84/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | ~ v1_funct_1(sK5) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1729]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2758,plain,
% 11.84/1.99      ( m1_subset_1(k1_partfun1(X0,X1,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 11.84/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.84/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | ~ v1_funct_1(sK5) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_2030]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_4296,plain,
% 11.84/1.99      ( m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.84/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.84/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | ~ v1_funct_1(sK5) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_2758]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_6852,plain,
% 11.84/1.99      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) ),
% 11.84/1.99      inference(global_propositional_subsumption,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_439,c_39,c_37,c_36,c_34,c_58,c_437,c_4296]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_7807,plain,
% 11.84/1.99      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k6_partfun1(sK2) ),
% 11.84/1.99      inference(resolution,[status(thm)],[c_3763,c_6852]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_8672,plain,
% 11.84/1.99      ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5))
% 11.84/1.99      | ~ v2_funct_1(k6_partfun1(sK2)) ),
% 11.84/1.99      inference(resolution,[status(thm)],[c_7807,c_750]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_19,plain,
% 11.84/1.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.84/1.99      inference(cnf_transformation,[],[f106]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_85,plain,
% 11.84/1.99      ( v2_funct_1(k6_partfun1(sK2)) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_11836,plain,
% 11.84/1.99      ( v2_funct_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)) ),
% 11.84/1.99      inference(global_propositional_subsumption,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_8672,c_85]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_12385,plain,
% 11.84/1.99      ( ~ v1_funct_2(sK4,sK2,sK3)
% 11.84/1.99      | ~ v1_funct_2(sK5,sK3,sK2)
% 11.84/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.84/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | ~ v1_funct_1(sK5)
% 11.84/1.99      | v2_funct_1(sK4)
% 11.84/1.99      | k1_xboole_0 = sK2 ),
% 11.84/1.99      inference(resolution,[status(thm)],[c_31,c_11836]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_10536,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0))
% 11.84/1.99      | ~ v1_xboole_0(k6_partfun1(X0)) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_10538,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2))
% 11.84/1.99      | ~ v1_xboole_0(k6_partfun1(sK2)) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_10536]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_10,plain,
% 11.84/1.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 11.84/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1368,plain,
% 11.84/1.99      ( v1_xboole_0(X0) != iProver_top
% 11.84/1.99      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1359,plain,
% 11.84/1.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_11,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.84/1.99      | ~ v1_xboole_0(X1)
% 11.84/1.99      | v1_xboole_0(X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1367,plain,
% 11.84/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.84/1.99      | v1_xboole_0(X1) != iProver_top
% 11.84/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3005,plain,
% 11.84/1.99      ( v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top
% 11.84/1.99      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_1359,c_1367]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5959,plain,
% 11.84/1.99      ( v1_xboole_0(X0) != iProver_top
% 11.84/1.99      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_1368,c_3005]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5960,plain,
% 11.84/1.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k6_partfun1(X0)) ),
% 11.84/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_5959]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5962,plain,
% 11.84/1.99      ( v1_xboole_0(k6_partfun1(sK2)) | ~ v1_xboole_0(sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_5960]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3,plain,
% 11.84/1.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5896,plain,
% 11.84/1.99      ( r1_tarski(X0,k6_partfun1(X1))
% 11.84/1.99      | r2_hidden(sK1(X0,k6_partfun1(X1)),X0) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5898,plain,
% 11.84/1.99      ( r1_tarski(sK2,k6_partfun1(sK2))
% 11.84/1.99      | r2_hidden(sK1(sK2,k6_partfun1(sK2)),sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_5896]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1352,plain,
% 11.84/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1355,plain,
% 11.84/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_29,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.84/1.99      | ~ v1_funct_1(X0)
% 11.84/1.99      | ~ v1_funct_1(X3)
% 11.84/1.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1358,plain,
% 11.84/1.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.84/1.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.84/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.84/1.99      | v1_funct_1(X5) != iProver_top
% 11.84/1.99      | v1_funct_1(X4) != iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_4651,plain,
% 11.84/1.99      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 11.84/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.84/1.99      | v1_funct_1(X2) != iProver_top
% 11.84/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_1355,c_1358]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_43,plain,
% 11.84/1.99      ( v1_funct_1(sK5) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5015,plain,
% 11.84/1.99      ( v1_funct_1(X2) != iProver_top
% 11.84/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.84/1.99      | k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5) ),
% 11.84/1.99      inference(global_propositional_subsumption,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_4651,c_43]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5016,plain,
% 11.84/1.99      ( k1_partfun1(X0,X1,sK3,sK2,X2,sK5) = k5_relat_1(X2,sK5)
% 11.84/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.84/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.84/1.99      inference(renaming,[status(thm)],[c_5015]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5027,plain,
% 11.84/1.99      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
% 11.84/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_1352,c_5016]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1739,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.84/1.99      | ~ v1_funct_1(X0)
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_29]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2010,plain,
% 11.84/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.84/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | ~ v1_funct_1(sK5)
% 11.84/1.99      | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1739]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2693,plain,
% 11.84/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.84/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | ~ v1_funct_1(sK5)
% 11.84/1.99      | k1_partfun1(X0,X1,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_2010]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_4284,plain,
% 11.84/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 11.84/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 11.84/1.99      | ~ v1_funct_1(sK4)
% 11.84/1.99      | ~ v1_funct_1(sK5)
% 11.84/1.99      | k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_2693]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5225,plain,
% 11.84/1.99      ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 11.84/1.99      inference(global_propositional_subsumption,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_5027,c_39,c_37,c_36,c_34,c_4284]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1348,plain,
% 11.84/1.99      ( k6_partfun1(sK2) = k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5)
% 11.84/1.99      | m1_subset_1(k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5228,plain,
% 11.84/1.99      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2)
% 11.84/1.99      | m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 11.84/1.99      inference(demodulation,[status(thm)],[c_5225,c_1348]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_40,plain,
% 11.84/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_42,plain,
% 11.84/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_45,plain,
% 11.84/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1361,plain,
% 11.84/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.84/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.84/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 11.84/1.99      | v1_funct_1(X0) != iProver_top
% 11.84/1.99      | v1_funct_1(X3) != iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5230,plain,
% 11.84/1.99      ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
% 11.84/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 11.84/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 11.84/1.99      | v1_funct_1(sK4) != iProver_top
% 11.84/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_5225,c_1361]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5724,plain,
% 11.84/1.99      ( k5_relat_1(sK4,sK5) = k6_partfun1(sK2) ),
% 11.84/1.99      inference(global_propositional_subsumption,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_5228,c_40,c_42,c_43,c_45,c_5230]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_16,plain,
% 11.84/1.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 11.84/1.99      | ~ v1_relat_1(X0)
% 11.84/1.99      | ~ v1_relat_1(X1) ),
% 11.84/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1364,plain,
% 11.84/1.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 11.84/1.99      | v1_relat_1(X0) != iProver_top
% 11.84/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5728,plain,
% 11.84/1.99      ( r1_tarski(k2_relat_1(k6_partfun1(sK2)),k2_relat_1(sK5)) = iProver_top
% 11.84/1.99      | v1_relat_1(sK4) != iProver_top
% 11.84/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_5724,c_1364]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_17,plain,
% 11.84/1.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 11.84/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5729,plain,
% 11.84/1.99      ( r1_tarski(sK2,k2_relat_1(sK5)) = iProver_top
% 11.84/1.99      | v1_relat_1(sK4) != iProver_top
% 11.84/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.84/1.99      inference(demodulation,[status(thm)],[c_5728,c_17]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5454,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(sK4,X0),sK4) | ~ v1_xboole_0(sK4) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5456,plain,
% 11.84/1.99      ( ~ r2_hidden(sK1(sK4,sK2),sK4) | ~ v1_xboole_0(sK4) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_5454]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3404,plain,
% 11.84/1.99      ( r1_tarski(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3406,plain,
% 11.84/1.99      ( r1_tarski(sK2,sK4) | r2_hidden(sK1(sK2,sK4),sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_3404]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3337,plain,
% 11.84/1.99      ( r1_tarski(k6_partfun1(X0),X1)
% 11.84/1.99      | r2_hidden(sK1(k6_partfun1(X0),X1),k6_partfun1(X0)) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3339,plain,
% 11.84/1.99      ( r1_tarski(k6_partfun1(sK2),sK2)
% 11.84/1.99      | r2_hidden(sK1(k6_partfun1(sK2),sK2),k6_partfun1(sK2)) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_3337]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3007,plain,
% 11.84/1.99      ( v1_xboole_0(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 11.84/1.99      | v1_xboole_0(sK4) = iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_1352,c_1367]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3279,plain,
% 11.84/1.99      ( v1_xboole_0(sK4) = iProver_top
% 11.84/1.99      | v1_xboole_0(sK2) != iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_1368,c_3007]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3280,plain,
% 11.84/1.99      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK2) ),
% 11.84/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_3279]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_21,plain,
% 11.84/1.99      ( v5_relat_1(X0,X1)
% 11.84/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.84/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_14,plain,
% 11.84/1.99      ( ~ v5_relat_1(X0,X1)
% 11.84/1.99      | r1_tarski(k2_relat_1(X0),X1)
% 11.84/1.99      | ~ v1_relat_1(X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_476,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.84/1.99      | r1_tarski(k2_relat_1(X0),X2)
% 11.84/1.99      | ~ v1_relat_1(X0) ),
% 11.84/1.99      inference(resolution,[status(thm)],[c_21,c_14]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1347,plain,
% 11.84/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.84/1.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 11.84/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2774,plain,
% 11.84/1.99      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top
% 11.84/1.99      | v1_relat_1(sK5) != iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_1355,c_1347]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_12,plain,
% 11.84/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.84/1.99      | ~ v1_relat_1(X1)
% 11.84/1.99      | v1_relat_1(X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2103,plain,
% 11.84/1.99      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK2)) | v1_relat_1(sK5) ),
% 11.84/1.99      inference(resolution,[status(thm)],[c_12,c_34]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_15,plain,
% 11.84/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.84/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2110,plain,
% 11.84/1.99      ( v1_relat_1(sK5) ),
% 11.84/1.99      inference(forward_subsumption_resolution,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_2103,c_15]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2111,plain,
% 11.84/1.99      ( v1_relat_1(sK5) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3050,plain,
% 11.84/1.99      ( r1_tarski(k2_relat_1(sK5),sK2) = iProver_top ),
% 11.84/1.99      inference(global_propositional_subsumption,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_2774,c_2111]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_5,plain,
% 11.84/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.84/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1370,plain,
% 11.84/1.99      ( X0 = X1
% 11.84/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.84/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_3055,plain,
% 11.84/1.99      ( k2_relat_1(sK5) = sK2
% 11.84/1.99      | r1_tarski(sK2,k2_relat_1(sK5)) != iProver_top ),
% 11.84/1.99      inference(superposition,[status(thm)],[c_3050,c_1370]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2446,plain,
% 11.84/1.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2448,plain,
% 11.84/1.99      ( ~ r1_tarski(sK4,sK2) | ~ r1_tarski(sK2,sK4) | sK4 = sK2 ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_2446]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2426,plain,
% 11.84/1.99      ( r1_tarski(sK4,X0) | r2_hidden(sK1(sK4,X0),sK4) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2428,plain,
% 11.84/1.99      ( r1_tarski(sK4,sK2) | r2_hidden(sK1(sK4,sK2),sK4) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_2426]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_13,plain,
% 11.84/1.99      ( v5_relat_1(X0,X1)
% 11.84/1.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.84/1.99      | ~ v1_relat_1(X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_24,plain,
% 11.84/1.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 11.84/1.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 11.84/1.99      | ~ v1_relat_1(X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_32,negated_conjecture,
% 11.84/1.99      ( ~ v2_funct_2(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 11.84/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_455,plain,
% 11.84/1.99      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 11.84/1.99      | ~ v2_funct_1(sK4)
% 11.84/1.99      | ~ v1_relat_1(X0)
% 11.84/1.99      | k2_relat_1(X0) != sK2
% 11.84/1.99      | sK5 != X0 ),
% 11.84/1.99      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_456,plain,
% 11.84/1.99      ( ~ v5_relat_1(sK5,k2_relat_1(sK5))
% 11.84/1.99      | ~ v2_funct_1(sK4)
% 11.84/1.99      | ~ v1_relat_1(sK5)
% 11.84/1.99      | k2_relat_1(sK5) != sK2 ),
% 11.84/1.99      inference(unflattening,[status(thm)],[c_455]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_509,plain,
% 11.84/1.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.84/1.99      | ~ v2_funct_1(sK4)
% 11.84/1.99      | ~ v1_relat_1(X0)
% 11.84/1.99      | ~ v1_relat_1(sK5)
% 11.84/1.99      | k2_relat_1(sK5) != X1
% 11.84/1.99      | k2_relat_1(sK5) != sK2
% 11.84/1.99      | sK5 != X0 ),
% 11.84/1.99      inference(resolution_lifted,[status(thm)],[c_13,c_456]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_510,plain,
% 11.84/1.99      ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5))
% 11.84/1.99      | ~ v2_funct_1(sK4)
% 11.84/1.99      | ~ v1_relat_1(sK5)
% 11.84/1.99      | k2_relat_1(sK5) != sK2 ),
% 11.84/1.99      inference(unflattening,[status(thm)],[c_509]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_6,plain,
% 11.84/1.99      ( r1_tarski(X0,X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f108]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_520,plain,
% 11.84/1.99      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK5) | k2_relat_1(sK5) != sK2 ),
% 11.84/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_510,c_6]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2362,plain,
% 11.84/1.99      ( ~ v2_funct_1(sK4) | k2_relat_1(sK5) != sK2 ),
% 11.84/1.99      inference(backward_subsumption_resolution,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_2110,c_520]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2105,plain,
% 11.84/1.99      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) | v1_relat_1(sK4) ),
% 11.84/1.99      inference(resolution,[status(thm)],[c_12,c_37]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2117,plain,
% 11.84/1.99      ( v1_relat_1(sK4) ),
% 11.84/1.99      inference(forward_subsumption_resolution,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_2105,c_15]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_2118,plain,
% 11.84/1.99      ( v1_relat_1(sK4) = iProver_top ),
% 11.84/1.99      inference(predicate_to_equality,[status(thm)],[c_2117]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1869,plain,
% 11.84/1.99      ( ~ r1_tarski(X0,k6_partfun1(X1))
% 11.84/1.99      | ~ r1_tarski(k6_partfun1(X1),X0)
% 11.84/1.99      | X0 = k6_partfun1(X1) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1871,plain,
% 11.84/1.99      ( ~ r1_tarski(k6_partfun1(sK2),sK2)
% 11.84/1.99      | ~ r1_tarski(sK2,k6_partfun1(sK2))
% 11.84/1.99      | sK2 = k6_partfun1(sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1869]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1642,plain,
% 11.84/1.99      ( v2_funct_1(X0)
% 11.84/1.99      | ~ v2_funct_1(k6_partfun1(X1))
% 11.84/1.99      | X0 != k6_partfun1(X1) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_750]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_1644,plain,
% 11.84/1.99      ( ~ v2_funct_1(k6_partfun1(sK2))
% 11.84/1.99      | v2_funct_1(sK2)
% 11.84/1.99      | sK2 != k6_partfun1(sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_1642]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_8,plain,
% 11.84/1.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_9,plain,
% 11.84/1.99      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_419,plain,
% 11.84/1.99      ( ~ r1_tarski(X0,X1)
% 11.84/1.99      | v1_xboole_0(X0)
% 11.84/1.99      | X0 != X2
% 11.84/1.99      | k1_xboole_0 != X1 ),
% 11.84/1.99      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_420,plain,
% 11.84/1.99      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 11.84/1.99      inference(unflattening,[status(thm)],[c_419]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_422,plain,
% 11.84/1.99      ( ~ r1_tarski(sK2,k1_xboole_0) | v1_xboole_0(sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_420]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_117,plain,
% 11.84/1.99      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_7,plain,
% 11.84/1.99      ( r1_tarski(X0,X0) ),
% 11.84/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_113,plain,
% 11.84/1.99      ( r1_tarski(sK2,sK2) ),
% 11.84/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_35,negated_conjecture,
% 11.84/1.99      ( v1_funct_2(sK5,sK3,sK2) ),
% 11.84/1.99      inference(cnf_transformation,[],[f100]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(c_38,negated_conjecture,
% 11.84/1.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 11.84/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.84/1.99  
% 11.84/1.99  cnf(contradiction,plain,
% 11.84/1.99      ( $false ),
% 11.84/1.99      inference(minisat,
% 11.84/1.99                [status(thm)],
% 11.84/1.99                [c_41920,c_22143,c_22129,c_14245,c_12385,c_10538,c_5962,
% 11.84/1.99                 c_5898,c_5729,c_5456,c_3406,c_3339,c_3280,c_3055,c_2448,
% 11.84/1.99                 c_2428,c_2362,c_2118,c_2111,c_1871,c_1644,c_422,c_117,
% 11.84/1.99                 c_113,c_85,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 11.84/1.99  
% 11.84/1.99  
% 11.84/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.84/1.99  
% 11.84/1.99  ------                               Statistics
% 11.84/1.99  
% 11.84/1.99  ------ Selected
% 11.84/1.99  
% 11.84/1.99  total_time:                             1.179
% 11.84/1.99  
%------------------------------------------------------------------------------

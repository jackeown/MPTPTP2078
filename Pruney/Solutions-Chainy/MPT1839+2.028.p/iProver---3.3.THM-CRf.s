%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:45 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 415 expanded)
%              Number of clauses        :   48 ( 114 expanded)
%              Number of leaves         :   18 ( 105 expanded)
%              Depth                    :   22
%              Number of atoms          :  280 (1401 expanded)
%              Number of equality atoms :  124 ( 315 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK6)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK5,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK5,X1)) )
      & v1_zfmisc_1(sK5)
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ~ r1_tarski(sK5,sK6)
    & ~ v1_xboole_0(k3_xboole_0(sK5,sK6))
    & v1_zfmisc_1(sK5)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f59,f58])).

fof(f97,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f24,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK4(X0)) = X0
        & m1_subset_1(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK4(X0)) = X0
            & m1_subset_1(sK4(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK4(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f114,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f52])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f99,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f60])).

fof(f111,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK6))) ),
    inference(definition_unfolding,[],[f99,f78])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ~ r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1753,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_436,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_34])).

cnf(c_437,plain,
    ( r2_hidden(sK0(sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_1740,plain,
    ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_30,plain,
    ( m1_subset_1(sK4(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_382,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | sK4(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_383,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK4(X0)) = k1_tarski(sK4(X0)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_33,negated_conjecture,
    ( v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_399,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK4(X0)) = k1_tarski(sK4(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_33])).

cnf(c_400,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK4(sK5)) = k1_tarski(sK4(sK5)) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_402,plain,
    ( k6_domain_1(sK5,sK4(sK5)) = k1_tarski(sK4(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_34])).

cnf(c_29,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_407,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK4(X0)) = X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_408,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK4(sK5)) = sK5 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_410,plain,
    ( k6_domain_1(sK5,sK4(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_34])).

cnf(c_1785,plain,
    ( k1_tarski(sK4(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_402,c_410])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1748,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3195,plain,
    ( sK4(sK5) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1748])).

cnf(c_3342,plain,
    ( sK4(sK5) = sK0(sK5) ),
    inference(superposition,[status(thm)],[c_1740,c_3195])).

cnf(c_3358,plain,
    ( k1_tarski(sK0(sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_3342,c_1785])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1745,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3962,plain,
    ( k1_tarski(sK0(sK5)) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3358,c_1745])).

cnf(c_3966,plain,
    ( sK5 = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3962,c_3358])).

cnf(c_4266,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = sK5
    | k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1753,c_3966])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4593,plain,
    ( k4_xboole_0(sK5,X0) = k5_xboole_0(sK5,sK5)
    | k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4266,c_0])).

cnf(c_14,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_16,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1779,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14,c_16])).

cnf(c_2470,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1779,c_0])).

cnf(c_2471,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2470,c_16,c_1779])).

cnf(c_4607,plain,
    ( k4_xboole_0(sK5,X0) = k1_xboole_0
    | k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4593,c_2471])).

cnf(c_6,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK6))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_452,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK6)) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_32])).

cnf(c_9149,plain,
    ( k4_xboole_0(sK5,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4607,c_452])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_223,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_656,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_223,c_31])).

cnf(c_657,plain,
    ( k4_xboole_0(sK5,sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9149,c_657])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.11/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.05  
% 3.11/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/1.05  
% 3.11/1.05  ------  iProver source info
% 3.11/1.05  
% 3.11/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.11/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/1.05  git: non_committed_changes: false
% 3.11/1.05  git: last_make_outside_of_git: false
% 3.11/1.05  
% 3.11/1.05  ------ 
% 3.11/1.05  
% 3.11/1.05  ------ Input Options
% 3.11/1.05  
% 3.11/1.05  --out_options                           all
% 3.11/1.05  --tptp_safe_out                         true
% 3.11/1.05  --problem_path                          ""
% 3.11/1.05  --include_path                          ""
% 3.11/1.05  --clausifier                            res/vclausify_rel
% 3.11/1.05  --clausifier_options                    --mode clausify
% 3.11/1.05  --stdin                                 false
% 3.11/1.05  --stats_out                             all
% 3.11/1.05  
% 3.11/1.05  ------ General Options
% 3.11/1.05  
% 3.11/1.05  --fof                                   false
% 3.11/1.05  --time_out_real                         305.
% 3.11/1.05  --time_out_virtual                      -1.
% 3.11/1.05  --symbol_type_check                     false
% 3.11/1.05  --clausify_out                          false
% 3.11/1.05  --sig_cnt_out                           false
% 3.11/1.05  --trig_cnt_out                          false
% 3.11/1.05  --trig_cnt_out_tolerance                1.
% 3.11/1.05  --trig_cnt_out_sk_spl                   false
% 3.11/1.05  --abstr_cl_out                          false
% 3.11/1.05  
% 3.11/1.05  ------ Global Options
% 3.11/1.05  
% 3.11/1.05  --schedule                              default
% 3.11/1.05  --add_important_lit                     false
% 3.11/1.05  --prop_solver_per_cl                    1000
% 3.11/1.05  --min_unsat_core                        false
% 3.11/1.05  --soft_assumptions                      false
% 3.11/1.05  --soft_lemma_size                       3
% 3.11/1.05  --prop_impl_unit_size                   0
% 3.11/1.05  --prop_impl_unit                        []
% 3.11/1.05  --share_sel_clauses                     true
% 3.11/1.05  --reset_solvers                         false
% 3.11/1.05  --bc_imp_inh                            [conj_cone]
% 3.11/1.05  --conj_cone_tolerance                   3.
% 3.11/1.05  --extra_neg_conj                        none
% 3.11/1.05  --large_theory_mode                     true
% 3.11/1.05  --prolific_symb_bound                   200
% 3.11/1.05  --lt_threshold                          2000
% 3.11/1.05  --clause_weak_htbl                      true
% 3.11/1.05  --gc_record_bc_elim                     false
% 3.11/1.05  
% 3.11/1.05  ------ Preprocessing Options
% 3.11/1.05  
% 3.11/1.05  --preprocessing_flag                    true
% 3.11/1.05  --time_out_prep_mult                    0.1
% 3.11/1.05  --splitting_mode                        input
% 3.11/1.05  --splitting_grd                         true
% 3.11/1.05  --splitting_cvd                         false
% 3.11/1.05  --splitting_cvd_svl                     false
% 3.11/1.05  --splitting_nvd                         32
% 3.11/1.05  --sub_typing                            true
% 3.11/1.05  --prep_gs_sim                           true
% 3.11/1.05  --prep_unflatten                        true
% 3.11/1.05  --prep_res_sim                          true
% 3.11/1.05  --prep_upred                            true
% 3.11/1.05  --prep_sem_filter                       exhaustive
% 3.11/1.05  --prep_sem_filter_out                   false
% 3.11/1.05  --pred_elim                             true
% 3.11/1.05  --res_sim_input                         true
% 3.11/1.05  --eq_ax_congr_red                       true
% 3.11/1.05  --pure_diseq_elim                       true
% 3.11/1.05  --brand_transform                       false
% 3.11/1.05  --non_eq_to_eq                          false
% 3.11/1.05  --prep_def_merge                        true
% 3.11/1.05  --prep_def_merge_prop_impl              false
% 3.11/1.05  --prep_def_merge_mbd                    true
% 3.11/1.05  --prep_def_merge_tr_red                 false
% 3.11/1.05  --prep_def_merge_tr_cl                  false
% 3.11/1.05  --smt_preprocessing                     true
% 3.11/1.05  --smt_ac_axioms                         fast
% 3.11/1.05  --preprocessed_out                      false
% 3.11/1.05  --preprocessed_stats                    false
% 3.11/1.05  
% 3.11/1.05  ------ Abstraction refinement Options
% 3.11/1.05  
% 3.11/1.05  --abstr_ref                             []
% 3.11/1.05  --abstr_ref_prep                        false
% 3.11/1.05  --abstr_ref_until_sat                   false
% 3.11/1.05  --abstr_ref_sig_restrict                funpre
% 3.11/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.05  --abstr_ref_under                       []
% 3.11/1.05  
% 3.11/1.05  ------ SAT Options
% 3.11/1.05  
% 3.11/1.05  --sat_mode                              false
% 3.11/1.05  --sat_fm_restart_options                ""
% 3.11/1.05  --sat_gr_def                            false
% 3.11/1.05  --sat_epr_types                         true
% 3.11/1.05  --sat_non_cyclic_types                  false
% 3.11/1.05  --sat_finite_models                     false
% 3.11/1.05  --sat_fm_lemmas                         false
% 3.11/1.05  --sat_fm_prep                           false
% 3.11/1.05  --sat_fm_uc_incr                        true
% 3.11/1.05  --sat_out_model                         small
% 3.11/1.05  --sat_out_clauses                       false
% 3.11/1.05  
% 3.11/1.05  ------ QBF Options
% 3.11/1.05  
% 3.11/1.05  --qbf_mode                              false
% 3.11/1.05  --qbf_elim_univ                         false
% 3.11/1.05  --qbf_dom_inst                          none
% 3.11/1.05  --qbf_dom_pre_inst                      false
% 3.11/1.05  --qbf_sk_in                             false
% 3.11/1.05  --qbf_pred_elim                         true
% 3.11/1.05  --qbf_split                             512
% 3.11/1.05  
% 3.11/1.05  ------ BMC1 Options
% 3.11/1.05  
% 3.11/1.05  --bmc1_incremental                      false
% 3.11/1.05  --bmc1_axioms                           reachable_all
% 3.11/1.05  --bmc1_min_bound                        0
% 3.11/1.05  --bmc1_max_bound                        -1
% 3.11/1.05  --bmc1_max_bound_default                -1
% 3.11/1.05  --bmc1_symbol_reachability              true
% 3.11/1.05  --bmc1_property_lemmas                  false
% 3.11/1.05  --bmc1_k_induction                      false
% 3.11/1.05  --bmc1_non_equiv_states                 false
% 3.11/1.05  --bmc1_deadlock                         false
% 3.11/1.05  --bmc1_ucm                              false
% 3.11/1.05  --bmc1_add_unsat_core                   none
% 3.11/1.05  --bmc1_unsat_core_children              false
% 3.11/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.05  --bmc1_out_stat                         full
% 3.11/1.05  --bmc1_ground_init                      false
% 3.11/1.05  --bmc1_pre_inst_next_state              false
% 3.11/1.05  --bmc1_pre_inst_state                   false
% 3.11/1.05  --bmc1_pre_inst_reach_state             false
% 3.11/1.05  --bmc1_out_unsat_core                   false
% 3.11/1.05  --bmc1_aig_witness_out                  false
% 3.11/1.05  --bmc1_verbose                          false
% 3.11/1.05  --bmc1_dump_clauses_tptp                false
% 3.11/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.05  --bmc1_dump_file                        -
% 3.11/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.05  --bmc1_ucm_extend_mode                  1
% 3.11/1.05  --bmc1_ucm_init_mode                    2
% 3.11/1.05  --bmc1_ucm_cone_mode                    none
% 3.11/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.05  --bmc1_ucm_relax_model                  4
% 3.11/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.05  --bmc1_ucm_layered_model                none
% 3.11/1.05  --bmc1_ucm_max_lemma_size               10
% 3.11/1.05  
% 3.11/1.05  ------ AIG Options
% 3.11/1.05  
% 3.11/1.05  --aig_mode                              false
% 3.11/1.05  
% 3.11/1.05  ------ Instantiation Options
% 3.11/1.05  
% 3.11/1.05  --instantiation_flag                    true
% 3.11/1.05  --inst_sos_flag                         false
% 3.11/1.05  --inst_sos_phase                        true
% 3.11/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.05  --inst_lit_sel_side                     num_symb
% 3.11/1.05  --inst_solver_per_active                1400
% 3.11/1.05  --inst_solver_calls_frac                1.
% 3.11/1.05  --inst_passive_queue_type               priority_queues
% 3.11/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.05  --inst_passive_queues_freq              [25;2]
% 3.11/1.05  --inst_dismatching                      true
% 3.11/1.05  --inst_eager_unprocessed_to_passive     true
% 3.11/1.05  --inst_prop_sim_given                   true
% 3.11/1.05  --inst_prop_sim_new                     false
% 3.11/1.05  --inst_subs_new                         false
% 3.11/1.05  --inst_eq_res_simp                      false
% 3.11/1.05  --inst_subs_given                       false
% 3.11/1.05  --inst_orphan_elimination               true
% 3.11/1.05  --inst_learning_loop_flag               true
% 3.11/1.05  --inst_learning_start                   3000
% 3.11/1.05  --inst_learning_factor                  2
% 3.11/1.05  --inst_start_prop_sim_after_learn       3
% 3.11/1.05  --inst_sel_renew                        solver
% 3.11/1.05  --inst_lit_activity_flag                true
% 3.11/1.05  --inst_restr_to_given                   false
% 3.11/1.05  --inst_activity_threshold               500
% 3.11/1.05  --inst_out_proof                        true
% 3.11/1.05  
% 3.11/1.05  ------ Resolution Options
% 3.11/1.05  
% 3.11/1.05  --resolution_flag                       true
% 3.11/1.05  --res_lit_sel                           adaptive
% 3.11/1.05  --res_lit_sel_side                      none
% 3.11/1.05  --res_ordering                          kbo
% 3.11/1.05  --res_to_prop_solver                    active
% 3.11/1.05  --res_prop_simpl_new                    false
% 3.11/1.05  --res_prop_simpl_given                  true
% 3.11/1.05  --res_passive_queue_type                priority_queues
% 3.11/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.05  --res_passive_queues_freq               [15;5]
% 3.11/1.05  --res_forward_subs                      full
% 3.11/1.05  --res_backward_subs                     full
% 3.11/1.05  --res_forward_subs_resolution           true
% 3.11/1.05  --res_backward_subs_resolution          true
% 3.11/1.05  --res_orphan_elimination                true
% 3.11/1.05  --res_time_limit                        2.
% 3.11/1.05  --res_out_proof                         true
% 3.11/1.05  
% 3.11/1.05  ------ Superposition Options
% 3.11/1.05  
% 3.11/1.05  --superposition_flag                    true
% 3.11/1.05  --sup_passive_queue_type                priority_queues
% 3.11/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.05  --demod_completeness_check              fast
% 3.11/1.05  --demod_use_ground                      true
% 3.11/1.05  --sup_to_prop_solver                    passive
% 3.11/1.05  --sup_prop_simpl_new                    true
% 3.11/1.05  --sup_prop_simpl_given                  true
% 3.11/1.05  --sup_fun_splitting                     false
% 3.11/1.05  --sup_smt_interval                      50000
% 3.11/1.05  
% 3.11/1.05  ------ Superposition Simplification Setup
% 3.11/1.05  
% 3.11/1.05  --sup_indices_passive                   []
% 3.11/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.05  --sup_full_bw                           [BwDemod]
% 3.11/1.05  --sup_immed_triv                        [TrivRules]
% 3.11/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.05  --sup_immed_bw_main                     []
% 3.11/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.05  
% 3.11/1.05  ------ Combination Options
% 3.11/1.05  
% 3.11/1.05  --comb_res_mult                         3
% 3.11/1.05  --comb_sup_mult                         2
% 3.11/1.05  --comb_inst_mult                        10
% 3.11/1.05  
% 3.11/1.05  ------ Debug Options
% 3.11/1.05  
% 3.11/1.05  --dbg_backtrace                         false
% 3.11/1.05  --dbg_dump_prop_clauses                 false
% 3.11/1.05  --dbg_dump_prop_clauses_file            -
% 3.11/1.05  --dbg_out_stat                          false
% 3.11/1.05  ------ Parsing...
% 3.11/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/1.05  
% 3.11/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.11/1.05  
% 3.11/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/1.05  
% 3.11/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/1.05  ------ Proving...
% 3.11/1.05  ------ Problem Properties 
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  clauses                                 33
% 3.11/1.05  conjectures                             1
% 3.11/1.05  EPR                                     6
% 3.11/1.05  Horn                                    29
% 3.11/1.05  unary                                   20
% 3.11/1.05  binary                                  7
% 3.11/1.05  lits                                    52
% 3.11/1.05  lits eq                                 22
% 3.11/1.05  fd_pure                                 0
% 3.11/1.05  fd_pseudo                               0
% 3.11/1.05  fd_cond                                 0
% 3.11/1.05  fd_pseudo_cond                          5
% 3.11/1.05  AC symbols                              0
% 3.11/1.05  
% 3.11/1.05  ------ Schedule dynamic 5 is on 
% 3.11/1.05  
% 3.11/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  ------ 
% 3.11/1.05  Current options:
% 3.11/1.05  ------ 
% 3.11/1.05  
% 3.11/1.05  ------ Input Options
% 3.11/1.05  
% 3.11/1.05  --out_options                           all
% 3.11/1.05  --tptp_safe_out                         true
% 3.11/1.05  --problem_path                          ""
% 3.11/1.05  --include_path                          ""
% 3.11/1.05  --clausifier                            res/vclausify_rel
% 3.11/1.05  --clausifier_options                    --mode clausify
% 3.11/1.05  --stdin                                 false
% 3.11/1.05  --stats_out                             all
% 3.11/1.05  
% 3.11/1.05  ------ General Options
% 3.11/1.05  
% 3.11/1.05  --fof                                   false
% 3.11/1.05  --time_out_real                         305.
% 3.11/1.05  --time_out_virtual                      -1.
% 3.11/1.05  --symbol_type_check                     false
% 3.11/1.05  --clausify_out                          false
% 3.11/1.05  --sig_cnt_out                           false
% 3.11/1.05  --trig_cnt_out                          false
% 3.11/1.05  --trig_cnt_out_tolerance                1.
% 3.11/1.05  --trig_cnt_out_sk_spl                   false
% 3.11/1.05  --abstr_cl_out                          false
% 3.11/1.05  
% 3.11/1.05  ------ Global Options
% 3.11/1.05  
% 3.11/1.05  --schedule                              default
% 3.11/1.05  --add_important_lit                     false
% 3.11/1.05  --prop_solver_per_cl                    1000
% 3.11/1.05  --min_unsat_core                        false
% 3.11/1.05  --soft_assumptions                      false
% 3.11/1.05  --soft_lemma_size                       3
% 3.11/1.05  --prop_impl_unit_size                   0
% 3.11/1.05  --prop_impl_unit                        []
% 3.11/1.05  --share_sel_clauses                     true
% 3.11/1.05  --reset_solvers                         false
% 3.11/1.05  --bc_imp_inh                            [conj_cone]
% 3.11/1.05  --conj_cone_tolerance                   3.
% 3.11/1.05  --extra_neg_conj                        none
% 3.11/1.05  --large_theory_mode                     true
% 3.11/1.05  --prolific_symb_bound                   200
% 3.11/1.05  --lt_threshold                          2000
% 3.11/1.05  --clause_weak_htbl                      true
% 3.11/1.05  --gc_record_bc_elim                     false
% 3.11/1.05  
% 3.11/1.05  ------ Preprocessing Options
% 3.11/1.05  
% 3.11/1.05  --preprocessing_flag                    true
% 3.11/1.05  --time_out_prep_mult                    0.1
% 3.11/1.05  --splitting_mode                        input
% 3.11/1.05  --splitting_grd                         true
% 3.11/1.05  --splitting_cvd                         false
% 3.11/1.05  --splitting_cvd_svl                     false
% 3.11/1.05  --splitting_nvd                         32
% 3.11/1.05  --sub_typing                            true
% 3.11/1.05  --prep_gs_sim                           true
% 3.11/1.05  --prep_unflatten                        true
% 3.11/1.05  --prep_res_sim                          true
% 3.11/1.05  --prep_upred                            true
% 3.11/1.05  --prep_sem_filter                       exhaustive
% 3.11/1.05  --prep_sem_filter_out                   false
% 3.11/1.05  --pred_elim                             true
% 3.11/1.05  --res_sim_input                         true
% 3.11/1.05  --eq_ax_congr_red                       true
% 3.11/1.05  --pure_diseq_elim                       true
% 3.11/1.05  --brand_transform                       false
% 3.11/1.05  --non_eq_to_eq                          false
% 3.11/1.05  --prep_def_merge                        true
% 3.11/1.05  --prep_def_merge_prop_impl              false
% 3.11/1.05  --prep_def_merge_mbd                    true
% 3.11/1.05  --prep_def_merge_tr_red                 false
% 3.11/1.05  --prep_def_merge_tr_cl                  false
% 3.11/1.05  --smt_preprocessing                     true
% 3.11/1.05  --smt_ac_axioms                         fast
% 3.11/1.05  --preprocessed_out                      false
% 3.11/1.05  --preprocessed_stats                    false
% 3.11/1.05  
% 3.11/1.05  ------ Abstraction refinement Options
% 3.11/1.05  
% 3.11/1.05  --abstr_ref                             []
% 3.11/1.05  --abstr_ref_prep                        false
% 3.11/1.05  --abstr_ref_until_sat                   false
% 3.11/1.05  --abstr_ref_sig_restrict                funpre
% 3.11/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.05  --abstr_ref_under                       []
% 3.11/1.05  
% 3.11/1.05  ------ SAT Options
% 3.11/1.05  
% 3.11/1.05  --sat_mode                              false
% 3.11/1.05  --sat_fm_restart_options                ""
% 3.11/1.05  --sat_gr_def                            false
% 3.11/1.05  --sat_epr_types                         true
% 3.11/1.05  --sat_non_cyclic_types                  false
% 3.11/1.05  --sat_finite_models                     false
% 3.11/1.05  --sat_fm_lemmas                         false
% 3.11/1.05  --sat_fm_prep                           false
% 3.11/1.05  --sat_fm_uc_incr                        true
% 3.11/1.05  --sat_out_model                         small
% 3.11/1.05  --sat_out_clauses                       false
% 3.11/1.05  
% 3.11/1.05  ------ QBF Options
% 3.11/1.05  
% 3.11/1.05  --qbf_mode                              false
% 3.11/1.05  --qbf_elim_univ                         false
% 3.11/1.05  --qbf_dom_inst                          none
% 3.11/1.05  --qbf_dom_pre_inst                      false
% 3.11/1.05  --qbf_sk_in                             false
% 3.11/1.05  --qbf_pred_elim                         true
% 3.11/1.05  --qbf_split                             512
% 3.11/1.05  
% 3.11/1.05  ------ BMC1 Options
% 3.11/1.05  
% 3.11/1.05  --bmc1_incremental                      false
% 3.11/1.05  --bmc1_axioms                           reachable_all
% 3.11/1.05  --bmc1_min_bound                        0
% 3.11/1.05  --bmc1_max_bound                        -1
% 3.11/1.05  --bmc1_max_bound_default                -1
% 3.11/1.05  --bmc1_symbol_reachability              true
% 3.11/1.05  --bmc1_property_lemmas                  false
% 3.11/1.05  --bmc1_k_induction                      false
% 3.11/1.05  --bmc1_non_equiv_states                 false
% 3.11/1.05  --bmc1_deadlock                         false
% 3.11/1.05  --bmc1_ucm                              false
% 3.11/1.05  --bmc1_add_unsat_core                   none
% 3.11/1.05  --bmc1_unsat_core_children              false
% 3.11/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.05  --bmc1_out_stat                         full
% 3.11/1.05  --bmc1_ground_init                      false
% 3.11/1.05  --bmc1_pre_inst_next_state              false
% 3.11/1.05  --bmc1_pre_inst_state                   false
% 3.11/1.05  --bmc1_pre_inst_reach_state             false
% 3.11/1.05  --bmc1_out_unsat_core                   false
% 3.11/1.05  --bmc1_aig_witness_out                  false
% 3.11/1.05  --bmc1_verbose                          false
% 3.11/1.05  --bmc1_dump_clauses_tptp                false
% 3.11/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.05  --bmc1_dump_file                        -
% 3.11/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.05  --bmc1_ucm_extend_mode                  1
% 3.11/1.05  --bmc1_ucm_init_mode                    2
% 3.11/1.05  --bmc1_ucm_cone_mode                    none
% 3.11/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.05  --bmc1_ucm_relax_model                  4
% 3.11/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.05  --bmc1_ucm_layered_model                none
% 3.11/1.05  --bmc1_ucm_max_lemma_size               10
% 3.11/1.05  
% 3.11/1.05  ------ AIG Options
% 3.11/1.05  
% 3.11/1.05  --aig_mode                              false
% 3.11/1.05  
% 3.11/1.05  ------ Instantiation Options
% 3.11/1.05  
% 3.11/1.05  --instantiation_flag                    true
% 3.11/1.05  --inst_sos_flag                         false
% 3.11/1.05  --inst_sos_phase                        true
% 3.11/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.05  --inst_lit_sel_side                     none
% 3.11/1.05  --inst_solver_per_active                1400
% 3.11/1.05  --inst_solver_calls_frac                1.
% 3.11/1.05  --inst_passive_queue_type               priority_queues
% 3.11/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.05  --inst_passive_queues_freq              [25;2]
% 3.11/1.05  --inst_dismatching                      true
% 3.11/1.05  --inst_eager_unprocessed_to_passive     true
% 3.11/1.05  --inst_prop_sim_given                   true
% 3.11/1.05  --inst_prop_sim_new                     false
% 3.11/1.05  --inst_subs_new                         false
% 3.11/1.05  --inst_eq_res_simp                      false
% 3.11/1.05  --inst_subs_given                       false
% 3.11/1.05  --inst_orphan_elimination               true
% 3.11/1.05  --inst_learning_loop_flag               true
% 3.11/1.05  --inst_learning_start                   3000
% 3.11/1.05  --inst_learning_factor                  2
% 3.11/1.05  --inst_start_prop_sim_after_learn       3
% 3.11/1.05  --inst_sel_renew                        solver
% 3.11/1.05  --inst_lit_activity_flag                true
% 3.11/1.05  --inst_restr_to_given                   false
% 3.11/1.05  --inst_activity_threshold               500
% 3.11/1.05  --inst_out_proof                        true
% 3.11/1.05  
% 3.11/1.05  ------ Resolution Options
% 3.11/1.05  
% 3.11/1.05  --resolution_flag                       false
% 3.11/1.05  --res_lit_sel                           adaptive
% 3.11/1.05  --res_lit_sel_side                      none
% 3.11/1.05  --res_ordering                          kbo
% 3.11/1.05  --res_to_prop_solver                    active
% 3.11/1.05  --res_prop_simpl_new                    false
% 3.11/1.05  --res_prop_simpl_given                  true
% 3.11/1.05  --res_passive_queue_type                priority_queues
% 3.11/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.05  --res_passive_queues_freq               [15;5]
% 3.11/1.05  --res_forward_subs                      full
% 3.11/1.05  --res_backward_subs                     full
% 3.11/1.05  --res_forward_subs_resolution           true
% 3.11/1.05  --res_backward_subs_resolution          true
% 3.11/1.05  --res_orphan_elimination                true
% 3.11/1.05  --res_time_limit                        2.
% 3.11/1.05  --res_out_proof                         true
% 3.11/1.05  
% 3.11/1.05  ------ Superposition Options
% 3.11/1.05  
% 3.11/1.05  --superposition_flag                    true
% 3.11/1.05  --sup_passive_queue_type                priority_queues
% 3.11/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.05  --demod_completeness_check              fast
% 3.11/1.05  --demod_use_ground                      true
% 3.11/1.05  --sup_to_prop_solver                    passive
% 3.11/1.05  --sup_prop_simpl_new                    true
% 3.11/1.05  --sup_prop_simpl_given                  true
% 3.11/1.05  --sup_fun_splitting                     false
% 3.11/1.05  --sup_smt_interval                      50000
% 3.11/1.05  
% 3.11/1.05  ------ Superposition Simplification Setup
% 3.11/1.05  
% 3.11/1.05  --sup_indices_passive                   []
% 3.11/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.05  --sup_full_bw                           [BwDemod]
% 3.11/1.05  --sup_immed_triv                        [TrivRules]
% 3.11/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.05  --sup_immed_bw_main                     []
% 3.11/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.05  
% 3.11/1.05  ------ Combination Options
% 3.11/1.05  
% 3.11/1.05  --comb_res_mult                         3
% 3.11/1.05  --comb_sup_mult                         2
% 3.11/1.05  --comb_inst_mult                        10
% 3.11/1.05  
% 3.11/1.05  ------ Debug Options
% 3.11/1.05  
% 3.11/1.05  --dbg_backtrace                         false
% 3.11/1.05  --dbg_dump_prop_clauses                 false
% 3.11/1.05  --dbg_dump_prop_clauses_file            -
% 3.11/1.05  --dbg_out_stat                          false
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  ------ Proving...
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  % SZS status Theorem for theBenchmark.p
% 3.11/1.05  
% 3.11/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/1.05  
% 3.11/1.05  fof(f8,axiom,(
% 3.11/1.05    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f73,plain,(
% 3.11/1.05    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.11/1.05    inference(cnf_transformation,[],[f8])).
% 3.11/1.05  
% 3.11/1.05  fof(f13,axiom,(
% 3.11/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f78,plain,(
% 3.11/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.11/1.05    inference(cnf_transformation,[],[f13])).
% 3.11/1.05  
% 3.11/1.05  fof(f106,plain,(
% 3.11/1.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 3.11/1.05    inference(definition_unfolding,[],[f73,f78])).
% 3.11/1.05  
% 3.11/1.05  fof(f1,axiom,(
% 3.11/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f36,plain,(
% 3.11/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.11/1.05    inference(nnf_transformation,[],[f1])).
% 3.11/1.05  
% 3.11/1.05  fof(f37,plain,(
% 3.11/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.11/1.05    inference(rectify,[],[f36])).
% 3.11/1.05  
% 3.11/1.05  fof(f38,plain,(
% 3.11/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.11/1.05    introduced(choice_axiom,[])).
% 3.11/1.05  
% 3.11/1.05  fof(f39,plain,(
% 3.11/1.05    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.11/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.11/1.05  
% 3.11/1.05  fof(f62,plain,(
% 3.11/1.05    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.11/1.05    inference(cnf_transformation,[],[f39])).
% 3.11/1.05  
% 3.11/1.05  fof(f25,conjecture,(
% 3.11/1.05    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f26,negated_conjecture,(
% 3.11/1.05    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 3.11/1.05    inference(negated_conjecture,[],[f25])).
% 3.11/1.05  
% 3.11/1.05  fof(f34,plain,(
% 3.11/1.05    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 3.11/1.05    inference(ennf_transformation,[],[f26])).
% 3.11/1.05  
% 3.11/1.05  fof(f35,plain,(
% 3.11/1.05    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 3.11/1.05    inference(flattening,[],[f34])).
% 3.11/1.05  
% 3.11/1.05  fof(f59,plain,(
% 3.11/1.05    ( ! [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) => (~r1_tarski(X0,sK6) & ~v1_xboole_0(k3_xboole_0(X0,sK6)))) )),
% 3.11/1.05    introduced(choice_axiom,[])).
% 3.11/1.05  
% 3.11/1.05  fof(f58,plain,(
% 3.11/1.05    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK5,X1) & ~v1_xboole_0(k3_xboole_0(sK5,X1))) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5))),
% 3.11/1.05    introduced(choice_axiom,[])).
% 3.11/1.05  
% 3.11/1.05  fof(f60,plain,(
% 3.11/1.05    (~r1_tarski(sK5,sK6) & ~v1_xboole_0(k3_xboole_0(sK5,sK6))) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5)),
% 3.11/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f59,f58])).
% 3.11/1.05  
% 3.11/1.05  fof(f97,plain,(
% 3.11/1.05    ~v1_xboole_0(sK5)),
% 3.11/1.05    inference(cnf_transformation,[],[f60])).
% 3.11/1.05  
% 3.11/1.05  fof(f23,axiom,(
% 3.11/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f31,plain,(
% 3.11/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.11/1.05    inference(ennf_transformation,[],[f23])).
% 3.11/1.05  
% 3.11/1.05  fof(f32,plain,(
% 3.11/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.11/1.05    inference(flattening,[],[f31])).
% 3.11/1.05  
% 3.11/1.05  fof(f93,plain,(
% 3.11/1.05    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.11/1.05    inference(cnf_transformation,[],[f32])).
% 3.11/1.05  
% 3.11/1.05  fof(f24,axiom,(
% 3.11/1.05    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f33,plain,(
% 3.11/1.05    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 3.11/1.05    inference(ennf_transformation,[],[f24])).
% 3.11/1.05  
% 3.11/1.05  fof(f54,plain,(
% 3.11/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.11/1.05    inference(nnf_transformation,[],[f33])).
% 3.11/1.05  
% 3.11/1.05  fof(f55,plain,(
% 3.11/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.11/1.05    inference(rectify,[],[f54])).
% 3.11/1.05  
% 3.11/1.05  fof(f56,plain,(
% 3.11/1.05    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)))),
% 3.11/1.05    introduced(choice_axiom,[])).
% 3.11/1.05  
% 3.11/1.05  fof(f57,plain,(
% 3.11/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.11/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 3.11/1.05  
% 3.11/1.05  fof(f94,plain,(
% 3.11/1.05    ( ! [X0] : (m1_subset_1(sK4(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.11/1.05    inference(cnf_transformation,[],[f57])).
% 3.11/1.05  
% 3.11/1.05  fof(f98,plain,(
% 3.11/1.05    v1_zfmisc_1(sK5)),
% 3.11/1.05    inference(cnf_transformation,[],[f60])).
% 3.11/1.05  
% 3.11/1.05  fof(f95,plain,(
% 3.11/1.05    ( ! [X0] : (k6_domain_1(X0,sK4(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.11/1.05    inference(cnf_transformation,[],[f57])).
% 3.11/1.05  
% 3.11/1.05  fof(f14,axiom,(
% 3.11/1.05    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f48,plain,(
% 3.11/1.05    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.11/1.05    inference(nnf_transformation,[],[f14])).
% 3.11/1.05  
% 3.11/1.05  fof(f49,plain,(
% 3.11/1.05    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.11/1.05    inference(rectify,[],[f48])).
% 3.11/1.05  
% 3.11/1.05  fof(f50,plain,(
% 3.11/1.05    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.11/1.05    introduced(choice_axiom,[])).
% 3.11/1.05  
% 3.11/1.05  fof(f51,plain,(
% 3.11/1.05    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.11/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 3.11/1.05  
% 3.11/1.05  fof(f79,plain,(
% 3.11/1.05    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.11/1.05    inference(cnf_transformation,[],[f51])).
% 3.11/1.05  
% 3.11/1.05  fof(f114,plain,(
% 3.11/1.05    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.11/1.05    inference(equality_resolution,[],[f79])).
% 3.11/1.05  
% 3.11/1.05  fof(f18,axiom,(
% 3.11/1.05    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f52,plain,(
% 3.11/1.05    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.11/1.05    inference(nnf_transformation,[],[f18])).
% 3.11/1.05  
% 3.11/1.05  fof(f53,plain,(
% 3.11/1.05    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.11/1.05    inference(flattening,[],[f52])).
% 3.11/1.05  
% 3.11/1.05  fof(f86,plain,(
% 3.11/1.05    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.11/1.05    inference(cnf_transformation,[],[f53])).
% 3.11/1.05  
% 3.11/1.05  fof(f7,axiom,(
% 3.11/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f72,plain,(
% 3.11/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.11/1.05    inference(cnf_transformation,[],[f7])).
% 3.11/1.05  
% 3.11/1.05  fof(f104,plain,(
% 3.11/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.11/1.05    inference(definition_unfolding,[],[f72,f78])).
% 3.11/1.05  
% 3.11/1.05  fof(f10,axiom,(
% 3.11/1.05    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f75,plain,(
% 3.11/1.05    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.11/1.05    inference(cnf_transformation,[],[f10])).
% 3.11/1.05  
% 3.11/1.05  fof(f108,plain,(
% 3.11/1.05    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.11/1.05    inference(definition_unfolding,[],[f75,f78])).
% 3.11/1.05  
% 3.11/1.05  fof(f12,axiom,(
% 3.11/1.05    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f77,plain,(
% 3.11/1.05    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.11/1.05    inference(cnf_transformation,[],[f12])).
% 3.11/1.05  
% 3.11/1.05  fof(f3,axiom,(
% 3.11/1.05    v1_xboole_0(k1_xboole_0)),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f66,plain,(
% 3.11/1.05    v1_xboole_0(k1_xboole_0)),
% 3.11/1.05    inference(cnf_transformation,[],[f3])).
% 3.11/1.05  
% 3.11/1.05  fof(f99,plain,(
% 3.11/1.05    ~v1_xboole_0(k3_xboole_0(sK5,sK6))),
% 3.11/1.05    inference(cnf_transformation,[],[f60])).
% 3.11/1.05  
% 3.11/1.05  fof(f111,plain,(
% 3.11/1.05    ~v1_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK6)))),
% 3.11/1.05    inference(definition_unfolding,[],[f99,f78])).
% 3.11/1.05  
% 3.11/1.05  fof(f6,axiom,(
% 3.11/1.05    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.05  
% 3.11/1.05  fof(f47,plain,(
% 3.11/1.05    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.11/1.05    inference(nnf_transformation,[],[f6])).
% 3.11/1.05  
% 3.11/1.05  fof(f70,plain,(
% 3.11/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.11/1.05    inference(cnf_transformation,[],[f47])).
% 3.11/1.05  
% 3.11/1.05  fof(f100,plain,(
% 3.11/1.05    ~r1_tarski(sK5,sK6)),
% 3.11/1.05    inference(cnf_transformation,[],[f60])).
% 3.11/1.05  
% 3.11/1.05  cnf(c_12,plain,
% 3.11/1.05      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 3.11/1.05      inference(cnf_transformation,[],[f106]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_1753,plain,
% 3.11/1.05      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.11/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_1,plain,
% 3.11/1.05      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.11/1.05      inference(cnf_transformation,[],[f62]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_34,negated_conjecture,
% 3.11/1.05      ( ~ v1_xboole_0(sK5) ),
% 3.11/1.05      inference(cnf_transformation,[],[f97]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_436,plain,
% 3.11/1.05      ( r2_hidden(sK0(X0),X0) | sK5 != X0 ),
% 3.11/1.05      inference(resolution_lifted,[status(thm)],[c_1,c_34]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_437,plain,
% 3.11/1.05      ( r2_hidden(sK0(sK5),sK5) ),
% 3.11/1.05      inference(unflattening,[status(thm)],[c_436]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_1740,plain,
% 3.11/1.05      ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
% 3.11/1.05      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_27,plain,
% 3.11/1.05      ( ~ m1_subset_1(X0,X1)
% 3.11/1.05      | v1_xboole_0(X1)
% 3.11/1.05      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.11/1.05      inference(cnf_transformation,[],[f93]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_30,plain,
% 3.11/1.05      ( m1_subset_1(sK4(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 3.11/1.05      inference(cnf_transformation,[],[f94]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_382,plain,
% 3.11/1.05      ( ~ v1_zfmisc_1(X0)
% 3.11/1.05      | v1_xboole_0(X1)
% 3.11/1.05      | v1_xboole_0(X0)
% 3.11/1.05      | X0 != X1
% 3.11/1.05      | k6_domain_1(X1,X2) = k1_tarski(X2)
% 3.11/1.05      | sK4(X0) != X2 ),
% 3.11/1.05      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_383,plain,
% 3.11/1.05      ( ~ v1_zfmisc_1(X0)
% 3.11/1.05      | v1_xboole_0(X0)
% 3.11/1.05      | k6_domain_1(X0,sK4(X0)) = k1_tarski(sK4(X0)) ),
% 3.11/1.05      inference(unflattening,[status(thm)],[c_382]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_33,negated_conjecture,
% 3.11/1.05      ( v1_zfmisc_1(sK5) ),
% 3.11/1.05      inference(cnf_transformation,[],[f98]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_399,plain,
% 3.11/1.05      ( v1_xboole_0(X0)
% 3.11/1.05      | k6_domain_1(X0,sK4(X0)) = k1_tarski(sK4(X0))
% 3.11/1.05      | sK5 != X0 ),
% 3.11/1.05      inference(resolution_lifted,[status(thm)],[c_383,c_33]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_400,plain,
% 3.11/1.05      ( v1_xboole_0(sK5)
% 3.11/1.05      | k6_domain_1(sK5,sK4(sK5)) = k1_tarski(sK4(sK5)) ),
% 3.11/1.05      inference(unflattening,[status(thm)],[c_399]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_402,plain,
% 3.11/1.05      ( k6_domain_1(sK5,sK4(sK5)) = k1_tarski(sK4(sK5)) ),
% 3.11/1.05      inference(global_propositional_subsumption,
% 3.11/1.05                [status(thm)],
% 3.11/1.05                [c_400,c_34]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_29,plain,
% 3.11/1.05      ( ~ v1_zfmisc_1(X0)
% 3.11/1.05      | v1_xboole_0(X0)
% 3.11/1.05      | k6_domain_1(X0,sK4(X0)) = X0 ),
% 3.11/1.05      inference(cnf_transformation,[],[f95]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_407,plain,
% 3.11/1.05      ( v1_xboole_0(X0) | k6_domain_1(X0,sK4(X0)) = X0 | sK5 != X0 ),
% 3.11/1.05      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_408,plain,
% 3.11/1.05      ( v1_xboole_0(sK5) | k6_domain_1(sK5,sK4(sK5)) = sK5 ),
% 3.11/1.05      inference(unflattening,[status(thm)],[c_407]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_410,plain,
% 3.11/1.05      ( k6_domain_1(sK5,sK4(sK5)) = sK5 ),
% 3.11/1.05      inference(global_propositional_subsumption,
% 3.11/1.05                [status(thm)],
% 3.11/1.05                [c_408,c_34]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_1785,plain,
% 3.11/1.05      ( k1_tarski(sK4(sK5)) = sK5 ),
% 3.11/1.05      inference(light_normalisation,[status(thm)],[c_402,c_410]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_20,plain,
% 3.11/1.05      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.11/1.05      inference(cnf_transformation,[],[f114]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_1748,plain,
% 3.11/1.05      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.11/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_3195,plain,
% 3.11/1.05      ( sK4(sK5) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.11/1.05      inference(superposition,[status(thm)],[c_1785,c_1748]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_3342,plain,
% 3.11/1.05      ( sK4(sK5) = sK0(sK5) ),
% 3.11/1.05      inference(superposition,[status(thm)],[c_1740,c_3195]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_3358,plain,
% 3.11/1.05      ( k1_tarski(sK0(sK5)) = sK5 ),
% 3.11/1.05      inference(demodulation,[status(thm)],[c_3342,c_1785]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_23,plain,
% 3.11/1.05      ( ~ r1_tarski(X0,k1_tarski(X1))
% 3.11/1.05      | k1_tarski(X1) = X0
% 3.11/1.05      | k1_xboole_0 = X0 ),
% 3.11/1.05      inference(cnf_transformation,[],[f86]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_1745,plain,
% 3.11/1.05      ( k1_tarski(X0) = X1
% 3.11/1.05      | k1_xboole_0 = X1
% 3.11/1.05      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 3.11/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_3962,plain,
% 3.11/1.05      ( k1_tarski(sK0(sK5)) = X0
% 3.11/1.05      | k1_xboole_0 = X0
% 3.11/1.05      | r1_tarski(X0,sK5) != iProver_top ),
% 3.11/1.05      inference(superposition,[status(thm)],[c_3358,c_1745]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_3966,plain,
% 3.11/1.05      ( sK5 = X0 | k1_xboole_0 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 3.11/1.05      inference(demodulation,[status(thm)],[c_3962,c_3358]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_4266,plain,
% 3.11/1.05      ( k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = sK5
% 3.11/1.05      | k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = k1_xboole_0 ),
% 3.11/1.05      inference(superposition,[status(thm)],[c_1753,c_3966]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_0,plain,
% 3.11/1.05      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.11/1.05      inference(cnf_transformation,[],[f104]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_4593,plain,
% 3.11/1.05      ( k4_xboole_0(sK5,X0) = k5_xboole_0(sK5,sK5)
% 3.11/1.05      | k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = k1_xboole_0 ),
% 3.11/1.05      inference(superposition,[status(thm)],[c_4266,c_0]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_14,plain,
% 3.11/1.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.11/1.05      inference(cnf_transformation,[],[f108]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_16,plain,
% 3.11/1.05      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.11/1.05      inference(cnf_transformation,[],[f77]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_1779,plain,
% 3.11/1.05      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.11/1.05      inference(light_normalisation,[status(thm)],[c_14,c_16]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_2470,plain,
% 3.11/1.05      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 3.11/1.05      inference(superposition,[status(thm)],[c_1779,c_0]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_2471,plain,
% 3.11/1.05      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.11/1.05      inference(light_normalisation,[status(thm)],[c_2470,c_16,c_1779]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_4607,plain,
% 3.11/1.05      ( k4_xboole_0(sK5,X0) = k1_xboole_0
% 3.11/1.05      | k4_xboole_0(sK5,k4_xboole_0(sK5,X0)) = k1_xboole_0 ),
% 3.11/1.05      inference(demodulation,[status(thm)],[c_4593,c_2471]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_6,plain,
% 3.11/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 3.11/1.05      inference(cnf_transformation,[],[f66]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_32,negated_conjecture,
% 3.11/1.05      ( ~ v1_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK6))) ),
% 3.11/1.05      inference(cnf_transformation,[],[f111]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_452,plain,
% 3.11/1.05      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK6)) != k1_xboole_0 ),
% 3.11/1.05      inference(resolution_lifted,[status(thm)],[c_6,c_32]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_9149,plain,
% 3.11/1.05      ( k4_xboole_0(sK5,sK6) = k1_xboole_0 ),
% 3.11/1.05      inference(superposition,[status(thm)],[c_4607,c_452]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_11,plain,
% 3.11/1.05      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.11/1.05      inference(cnf_transformation,[],[f70]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_223,plain,
% 3.11/1.05      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.11/1.05      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_31,negated_conjecture,
% 3.11/1.05      ( ~ r1_tarski(sK5,sK6) ),
% 3.11/1.05      inference(cnf_transformation,[],[f100]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_656,plain,
% 3.11/1.05      ( k4_xboole_0(X0,X1) != k1_xboole_0 | sK6 != X1 | sK5 != X0 ),
% 3.11/1.05      inference(resolution_lifted,[status(thm)],[c_223,c_31]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(c_657,plain,
% 3.11/1.05      ( k4_xboole_0(sK5,sK6) != k1_xboole_0 ),
% 3.11/1.05      inference(unflattening,[status(thm)],[c_656]) ).
% 3.11/1.05  
% 3.11/1.05  cnf(contradiction,plain,
% 3.11/1.05      ( $false ),
% 3.11/1.05      inference(minisat,[status(thm)],[c_9149,c_657]) ).
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/1.05  
% 3.11/1.05  ------                               Statistics
% 3.11/1.05  
% 3.11/1.05  ------ General
% 3.11/1.05  
% 3.11/1.05  abstr_ref_over_cycles:                  0
% 3.11/1.05  abstr_ref_under_cycles:                 0
% 3.11/1.05  gc_basic_clause_elim:                   0
% 3.11/1.05  forced_gc_time:                         0
% 3.11/1.05  parsing_time:                           0.011
% 3.11/1.05  unif_index_cands_time:                  0.
% 3.11/1.05  unif_index_add_time:                    0.
% 3.11/1.05  orderings_time:                         0.
% 3.11/1.05  out_proof_time:                         0.007
% 3.11/1.05  total_time:                             0.266
% 3.11/1.05  num_of_symbols:                         51
% 3.11/1.05  num_of_terms:                           8177
% 3.11/1.05  
% 3.11/1.05  ------ Preprocessing
% 3.11/1.05  
% 3.11/1.05  num_of_splits:                          0
% 3.11/1.05  num_of_split_atoms:                     0
% 3.11/1.05  num_of_reused_defs:                     0
% 3.11/1.05  num_eq_ax_congr_red:                    26
% 3.11/1.05  num_of_sem_filtered_clauses:            1
% 3.11/1.05  num_of_subtypes:                        0
% 3.11/1.05  monotx_restored_types:                  0
% 3.11/1.05  sat_num_of_epr_types:                   0
% 3.11/1.05  sat_num_of_non_cyclic_types:            0
% 3.11/1.05  sat_guarded_non_collapsed_types:        0
% 3.11/1.05  num_pure_diseq_elim:                    0
% 3.11/1.05  simp_replaced_by:                       0
% 3.11/1.05  res_preprocessed:                       161
% 3.11/1.05  prep_upred:                             0
% 3.11/1.05  prep_unflattend:                        98
% 3.11/1.05  smt_new_axioms:                         0
% 3.11/1.05  pred_elim_cands:                        2
% 3.11/1.05  pred_elim:                              3
% 3.11/1.05  pred_elim_cl:                           2
% 3.11/1.05  pred_elim_cycles:                       5
% 3.11/1.05  merged_defs:                            8
% 3.11/1.05  merged_defs_ncl:                        0
% 3.11/1.05  bin_hyper_res:                          8
% 3.11/1.05  prep_cycles:                            4
% 3.11/1.05  pred_elim_time:                         0.013
% 3.11/1.05  splitting_time:                         0.
% 3.11/1.05  sem_filter_time:                        0.
% 3.11/1.05  monotx_time:                            0.
% 3.11/1.05  subtype_inf_time:                       0.
% 3.11/1.05  
% 3.11/1.05  ------ Problem properties
% 3.11/1.05  
% 3.11/1.05  clauses:                                33
% 3.11/1.05  conjectures:                            1
% 3.11/1.05  epr:                                    6
% 3.11/1.05  horn:                                   29
% 3.11/1.05  ground:                                 7
% 3.11/1.05  unary:                                  20
% 3.11/1.05  binary:                                 7
% 3.11/1.05  lits:                                   52
% 3.11/1.05  lits_eq:                                22
% 3.11/1.05  fd_pure:                                0
% 3.11/1.05  fd_pseudo:                              0
% 3.11/1.05  fd_cond:                                0
% 3.11/1.05  fd_pseudo_cond:                         5
% 3.11/1.05  ac_symbols:                             0
% 3.11/1.05  
% 3.11/1.05  ------ Propositional Solver
% 3.11/1.05  
% 3.11/1.05  prop_solver_calls:                      27
% 3.11/1.05  prop_fast_solver_calls:                 846
% 3.11/1.05  smt_solver_calls:                       0
% 3.11/1.05  smt_fast_solver_calls:                  0
% 3.11/1.05  prop_num_of_clauses:                    3470
% 3.11/1.05  prop_preprocess_simplified:             9921
% 3.11/1.05  prop_fo_subsumed:                       9
% 3.11/1.05  prop_solver_time:                       0.
% 3.11/1.05  smt_solver_time:                        0.
% 3.11/1.05  smt_fast_solver_time:                   0.
% 3.11/1.05  prop_fast_solver_time:                  0.
% 3.11/1.05  prop_unsat_core_time:                   0.
% 3.11/1.05  
% 3.11/1.05  ------ QBF
% 3.11/1.05  
% 3.11/1.05  qbf_q_res:                              0
% 3.11/1.05  qbf_num_tautologies:                    0
% 3.11/1.05  qbf_prep_cycles:                        0
% 3.11/1.05  
% 3.11/1.05  ------ BMC1
% 3.11/1.05  
% 3.11/1.05  bmc1_current_bound:                     -1
% 3.11/1.05  bmc1_last_solved_bound:                 -1
% 3.11/1.05  bmc1_unsat_core_size:                   -1
% 3.11/1.05  bmc1_unsat_core_parents_size:           -1
% 3.11/1.05  bmc1_merge_next_fun:                    0
% 3.11/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.11/1.05  
% 3.11/1.05  ------ Instantiation
% 3.11/1.05  
% 3.11/1.05  inst_num_of_clauses:                    1195
% 3.11/1.05  inst_num_in_passive:                    474
% 3.11/1.05  inst_num_in_active:                     341
% 3.11/1.05  inst_num_in_unprocessed:                387
% 3.11/1.05  inst_num_of_loops:                      400
% 3.11/1.05  inst_num_of_learning_restarts:          0
% 3.11/1.05  inst_num_moves_active_passive:          58
% 3.11/1.05  inst_lit_activity:                      0
% 3.11/1.05  inst_lit_activity_moves:                0
% 3.11/1.05  inst_num_tautologies:                   0
% 3.11/1.05  inst_num_prop_implied:                  0
% 3.11/1.05  inst_num_existing_simplified:           0
% 3.11/1.05  inst_num_eq_res_simplified:             0
% 3.11/1.05  inst_num_child_elim:                    0
% 3.11/1.05  inst_num_of_dismatching_blockings:      189
% 3.11/1.05  inst_num_of_non_proper_insts:           793
% 3.11/1.05  inst_num_of_duplicates:                 0
% 3.11/1.05  inst_inst_num_from_inst_to_res:         0
% 3.11/1.05  inst_dismatching_checking_time:         0.
% 3.11/1.05  
% 3.11/1.05  ------ Resolution
% 3.11/1.05  
% 3.11/1.05  res_num_of_clauses:                     0
% 3.11/1.05  res_num_in_passive:                     0
% 3.11/1.05  res_num_in_active:                      0
% 3.11/1.05  res_num_of_loops:                       165
% 3.11/1.05  res_forward_subset_subsumed:            98
% 3.11/1.05  res_backward_subset_subsumed:           18
% 3.11/1.05  res_forward_subsumed:                   4
% 3.11/1.05  res_backward_subsumed:                  0
% 3.11/1.05  res_forward_subsumption_resolution:     0
% 3.11/1.05  res_backward_subsumption_resolution:    0
% 3.11/1.05  res_clause_to_clause_subsumption:       498
% 3.11/1.05  res_orphan_elimination:                 0
% 3.11/1.05  res_tautology_del:                      49
% 3.11/1.05  res_num_eq_res_simplified:              0
% 3.11/1.05  res_num_sel_changes:                    0
% 3.11/1.05  res_moves_from_active_to_pass:          0
% 3.11/1.05  
% 3.11/1.05  ------ Superposition
% 3.11/1.05  
% 3.11/1.05  sup_time_total:                         0.
% 3.11/1.05  sup_time_generating:                    0.
% 3.11/1.05  sup_time_sim_full:                      0.
% 3.11/1.05  sup_time_sim_immed:                     0.
% 3.11/1.05  
% 3.11/1.05  sup_num_of_clauses:                     117
% 3.11/1.05  sup_num_in_active:                      75
% 3.11/1.05  sup_num_in_passive:                     42
% 3.11/1.05  sup_num_of_loops:                       78
% 3.11/1.05  sup_fw_superposition:                   121
% 3.11/1.05  sup_bw_superposition:                   162
% 3.11/1.05  sup_immediate_simplified:               130
% 3.11/1.05  sup_given_eliminated:                   1
% 3.11/1.05  comparisons_done:                       0
% 3.11/1.05  comparisons_avoided:                    31
% 3.11/1.05  
% 3.11/1.05  ------ Simplifications
% 3.11/1.05  
% 3.11/1.05  
% 3.11/1.05  sim_fw_subset_subsumed:                 48
% 3.11/1.05  sim_bw_subset_subsumed:                 0
% 3.11/1.05  sim_fw_subsumed:                        37
% 3.11/1.05  sim_bw_subsumed:                        2
% 3.11/1.05  sim_fw_subsumption_res:                 0
% 3.11/1.05  sim_bw_subsumption_res:                 0
% 3.11/1.05  sim_tautology_del:                      4
% 3.11/1.05  sim_eq_tautology_del:                   48
% 3.11/1.05  sim_eq_res_simp:                        0
% 3.11/1.05  sim_fw_demodulated:                     37
% 3.11/1.05  sim_bw_demodulated:                     4
% 3.11/1.05  sim_light_normalised:                   31
% 3.11/1.05  sim_joinable_taut:                      0
% 3.11/1.05  sim_joinable_simp:                      0
% 3.11/1.05  sim_ac_normalised:                      0
% 3.11/1.05  sim_smt_subsumption:                    0
% 3.11/1.05  
%------------------------------------------------------------------------------

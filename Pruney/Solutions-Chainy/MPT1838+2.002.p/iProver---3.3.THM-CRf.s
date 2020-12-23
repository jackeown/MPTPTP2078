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
% DateTime   : Thu Dec  3 12:24:31 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  133 (2185 expanded)
%              Number of clauses        :   64 ( 555 expanded)
%              Number of leaves         :   19 ( 552 expanded)
%              Depth                    :   25
%              Number of atoms          :  372 (9063 expanded)
%              Number of equality atoms :  185 (2732 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK6 != X0
        & r1_tarski(X0,sK6)
        & v1_zfmisc_1(sK6)
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK5 != X1
          & r1_tarski(sK5,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( sK5 != sK6
    & r1_tarski(sK5,sK6)
    & v1_zfmisc_1(sK6)
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f51,f50])).

fof(f87,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f76,f69])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k5_xboole_0(X1,k4_xboole_0(X2,X1)) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f77,f69,f75])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f80,f75])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK4(X0)) = X0
        & m1_subset_1(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK4(X0)) = X0
            & m1_subset_1(sK4(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    v1_zfmisc_1(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK4(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f71,f75])).

fof(f110,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f88,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1372,plain,
    ( r1_tarski(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1379,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3001,plain,
    ( k4_xboole_0(sK5,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1372,c_1379])).

cnf(c_21,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3211,plain,
    ( k3_tarski(k2_tarski(sK6,sK5)) = k5_xboole_0(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3001,c_21])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_15,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1405,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_13,c_15])).

cnf(c_3213,plain,
    ( k3_tarski(k2_tarski(sK6,sK5)) = sK6 ),
    inference(demodulation,[status(thm)],[c_3211,c_1405])).

cnf(c_22,plain,
    ( X0 = X1
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_tarski(X2,X2)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1470,plain,
    ( X0 = X1
    | k3_tarski(k2_tarski(X1,X0)) != k2_tarski(X2,X2)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(light_normalisation,[status(thm)],[c_22,c_21])).

cnf(c_5599,plain,
    ( k2_tarski(X0,X0) != sK6
    | sK6 = sK5
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3213,c_1470])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_424,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_32])).

cnf(c_425,plain,
    ( r2_hidden(sK0(sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_426,plain,
    ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) = X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1375,plain,
    ( sK3(X0,X1) = X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1386,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3890,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1386])).

cnf(c_5016,plain,
    ( sK3(X0,sK5) = X0
    | k2_tarski(X0,X0) = sK5
    | r2_hidden(sK3(X0,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_3890])).

cnf(c_1369,plain,
    ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_4227,plain,
    ( r2_hidden(sK0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_3890])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_417,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_31])).

cnf(c_418,plain,
    ( r2_hidden(sK0(sK6),sK6) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1370,plain,
    ( r2_hidden(sK0(sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_27,plain,
    ( m1_subset_1(sK4(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_368,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | sK4(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_369,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK4(X0)) = k2_tarski(sK4(X0),sK4(X0)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_30,negated_conjecture,
    ( v1_zfmisc_1(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_387,plain,
    ( v1_xboole_0(X0)
    | k2_tarski(sK4(X0),sK4(X0)) = k6_domain_1(X0,sK4(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_369,c_30])).

cnf(c_388,plain,
    ( v1_xboole_0(sK6)
    | k2_tarski(sK4(sK6),sK4(sK6)) = k6_domain_1(sK6,sK4(sK6)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_390,plain,
    ( k2_tarski(sK4(sK6),sK4(sK6)) = k6_domain_1(sK6,sK4(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_31])).

cnf(c_26,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_395,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK4(X0)) = X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_396,plain,
    ( v1_xboole_0(sK6)
    | k6_domain_1(sK6,sK4(sK6)) = sK6 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_398,plain,
    ( k6_domain_1(sK6,sK4(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_31])).

cnf(c_1408,plain,
    ( k2_tarski(sK4(sK6),sK4(sK6)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_390,c_398])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1373,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2990,plain,
    ( sK4(sK6) = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_1373])).

cnf(c_3218,plain,
    ( sK4(sK6) = sK0(sK6) ),
    inference(superposition,[status(thm)],[c_1370,c_2990])).

cnf(c_3221,plain,
    ( sK0(sK6) = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3218,c_2990])).

cnf(c_4240,plain,
    ( sK0(sK5) = sK0(sK6) ),
    inference(superposition,[status(thm)],[c_4227,c_3221])).

cnf(c_4384,plain,
    ( sK0(sK5) = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4240,c_3221])).

cnf(c_6249,plain,
    ( sK3(X0,sK5) = X0
    | sK3(X0,sK5) = sK0(sK5)
    | k2_tarski(X0,X0) = sK5 ),
    inference(superposition,[status(thm)],[c_5016,c_4384])).

cnf(c_3604,plain,
    ( k2_tarski(sK0(sK6),sK0(sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_3218,c_1408])).

cnf(c_4385,plain,
    ( k2_tarski(sK0(sK5),sK0(sK5)) = sK6 ),
    inference(demodulation,[status(thm)],[c_4240,c_3604])).

cnf(c_6282,plain,
    ( sK3(sK0(sK5),sK5) = sK0(sK5)
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_6249,c_4385])).

cnf(c_17,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) != X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1376,plain,
    ( sK3(X0,X1) != X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK3(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6938,plain,
    ( k2_tarski(sK0(sK5),sK0(sK5)) = sK5
    | sK6 = sK5
    | r2_hidden(sK3(sK0(sK5),sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6282,c_1376])).

cnf(c_6944,plain,
    ( sK6 = sK5
    | r2_hidden(sK3(sK0(sK5),sK5),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6938,c_4385])).

cnf(c_6954,plain,
    ( sK6 = sK5
    | r2_hidden(sK0(sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6282,c_6944])).

cnf(c_19425,plain,
    ( sK6 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5599,c_426,c_6954])).

cnf(c_28,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_19481,plain,
    ( sK5 != sK5 ),
    inference(demodulation,[status(thm)],[c_19425,c_28])).

cnf(c_19482,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19481])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:53:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.29/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.03  
% 3.29/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/1.03  
% 3.29/1.03  ------  iProver source info
% 3.29/1.03  
% 3.29/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.29/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/1.03  git: non_committed_changes: false
% 3.29/1.03  git: last_make_outside_of_git: false
% 3.29/1.03  
% 3.29/1.03  ------ 
% 3.29/1.03  
% 3.29/1.03  ------ Input Options
% 3.29/1.03  
% 3.29/1.03  --out_options                           all
% 3.29/1.03  --tptp_safe_out                         true
% 3.29/1.03  --problem_path                          ""
% 3.29/1.03  --include_path                          ""
% 3.29/1.03  --clausifier                            res/vclausify_rel
% 3.29/1.03  --clausifier_options                    --mode clausify
% 3.29/1.03  --stdin                                 false
% 3.29/1.03  --stats_out                             all
% 3.29/1.03  
% 3.29/1.03  ------ General Options
% 3.29/1.03  
% 3.29/1.03  --fof                                   false
% 3.29/1.03  --time_out_real                         305.
% 3.29/1.03  --time_out_virtual                      -1.
% 3.29/1.03  --symbol_type_check                     false
% 3.29/1.03  --clausify_out                          false
% 3.29/1.03  --sig_cnt_out                           false
% 3.29/1.03  --trig_cnt_out                          false
% 3.29/1.03  --trig_cnt_out_tolerance                1.
% 3.29/1.03  --trig_cnt_out_sk_spl                   false
% 3.29/1.03  --abstr_cl_out                          false
% 3.29/1.03  
% 3.29/1.03  ------ Global Options
% 3.29/1.03  
% 3.29/1.03  --schedule                              default
% 3.29/1.03  --add_important_lit                     false
% 3.29/1.03  --prop_solver_per_cl                    1000
% 3.29/1.03  --min_unsat_core                        false
% 3.29/1.03  --soft_assumptions                      false
% 3.29/1.03  --soft_lemma_size                       3
% 3.29/1.03  --prop_impl_unit_size                   0
% 3.29/1.03  --prop_impl_unit                        []
% 3.29/1.03  --share_sel_clauses                     true
% 3.29/1.03  --reset_solvers                         false
% 3.29/1.03  --bc_imp_inh                            [conj_cone]
% 3.29/1.03  --conj_cone_tolerance                   3.
% 3.29/1.03  --extra_neg_conj                        none
% 3.29/1.03  --large_theory_mode                     true
% 3.29/1.03  --prolific_symb_bound                   200
% 3.29/1.03  --lt_threshold                          2000
% 3.29/1.03  --clause_weak_htbl                      true
% 3.29/1.03  --gc_record_bc_elim                     false
% 3.29/1.03  
% 3.29/1.03  ------ Preprocessing Options
% 3.29/1.03  
% 3.29/1.03  --preprocessing_flag                    true
% 3.29/1.03  --time_out_prep_mult                    0.1
% 3.29/1.03  --splitting_mode                        input
% 3.29/1.03  --splitting_grd                         true
% 3.29/1.03  --splitting_cvd                         false
% 3.29/1.03  --splitting_cvd_svl                     false
% 3.29/1.03  --splitting_nvd                         32
% 3.29/1.03  --sub_typing                            true
% 3.29/1.03  --prep_gs_sim                           true
% 3.29/1.03  --prep_unflatten                        true
% 3.29/1.03  --prep_res_sim                          true
% 3.29/1.03  --prep_upred                            true
% 3.29/1.03  --prep_sem_filter                       exhaustive
% 3.29/1.03  --prep_sem_filter_out                   false
% 3.29/1.03  --pred_elim                             true
% 3.29/1.03  --res_sim_input                         true
% 3.29/1.03  --eq_ax_congr_red                       true
% 3.29/1.03  --pure_diseq_elim                       true
% 3.29/1.03  --brand_transform                       false
% 3.29/1.03  --non_eq_to_eq                          false
% 3.29/1.03  --prep_def_merge                        true
% 3.29/1.03  --prep_def_merge_prop_impl              false
% 3.29/1.03  --prep_def_merge_mbd                    true
% 3.29/1.03  --prep_def_merge_tr_red                 false
% 3.29/1.03  --prep_def_merge_tr_cl                  false
% 3.29/1.03  --smt_preprocessing                     true
% 3.29/1.03  --smt_ac_axioms                         fast
% 3.29/1.03  --preprocessed_out                      false
% 3.29/1.03  --preprocessed_stats                    false
% 3.29/1.03  
% 3.29/1.03  ------ Abstraction refinement Options
% 3.29/1.03  
% 3.29/1.03  --abstr_ref                             []
% 3.29/1.03  --abstr_ref_prep                        false
% 3.29/1.03  --abstr_ref_until_sat                   false
% 3.29/1.03  --abstr_ref_sig_restrict                funpre
% 3.29/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/1.03  --abstr_ref_under                       []
% 3.29/1.03  
% 3.29/1.03  ------ SAT Options
% 3.29/1.03  
% 3.29/1.03  --sat_mode                              false
% 3.29/1.03  --sat_fm_restart_options                ""
% 3.29/1.03  --sat_gr_def                            false
% 3.29/1.03  --sat_epr_types                         true
% 3.29/1.03  --sat_non_cyclic_types                  false
% 3.29/1.03  --sat_finite_models                     false
% 3.29/1.03  --sat_fm_lemmas                         false
% 3.29/1.03  --sat_fm_prep                           false
% 3.29/1.03  --sat_fm_uc_incr                        true
% 3.29/1.03  --sat_out_model                         small
% 3.29/1.03  --sat_out_clauses                       false
% 3.29/1.03  
% 3.29/1.03  ------ QBF Options
% 3.29/1.03  
% 3.29/1.03  --qbf_mode                              false
% 3.29/1.03  --qbf_elim_univ                         false
% 3.29/1.03  --qbf_dom_inst                          none
% 3.29/1.03  --qbf_dom_pre_inst                      false
% 3.29/1.03  --qbf_sk_in                             false
% 3.29/1.03  --qbf_pred_elim                         true
% 3.29/1.03  --qbf_split                             512
% 3.29/1.03  
% 3.29/1.03  ------ BMC1 Options
% 3.29/1.03  
% 3.29/1.03  --bmc1_incremental                      false
% 3.29/1.03  --bmc1_axioms                           reachable_all
% 3.29/1.03  --bmc1_min_bound                        0
% 3.29/1.03  --bmc1_max_bound                        -1
% 3.29/1.03  --bmc1_max_bound_default                -1
% 3.29/1.03  --bmc1_symbol_reachability              true
% 3.29/1.03  --bmc1_property_lemmas                  false
% 3.29/1.03  --bmc1_k_induction                      false
% 3.29/1.03  --bmc1_non_equiv_states                 false
% 3.29/1.03  --bmc1_deadlock                         false
% 3.29/1.03  --bmc1_ucm                              false
% 3.29/1.03  --bmc1_add_unsat_core                   none
% 3.29/1.03  --bmc1_unsat_core_children              false
% 3.29/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/1.03  --bmc1_out_stat                         full
% 3.29/1.03  --bmc1_ground_init                      false
% 3.29/1.03  --bmc1_pre_inst_next_state              false
% 3.29/1.03  --bmc1_pre_inst_state                   false
% 3.29/1.03  --bmc1_pre_inst_reach_state             false
% 3.29/1.03  --bmc1_out_unsat_core                   false
% 3.29/1.03  --bmc1_aig_witness_out                  false
% 3.29/1.03  --bmc1_verbose                          false
% 3.29/1.03  --bmc1_dump_clauses_tptp                false
% 3.29/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.29/1.03  --bmc1_dump_file                        -
% 3.29/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.29/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.29/1.03  --bmc1_ucm_extend_mode                  1
% 3.29/1.03  --bmc1_ucm_init_mode                    2
% 3.29/1.03  --bmc1_ucm_cone_mode                    none
% 3.29/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.29/1.03  --bmc1_ucm_relax_model                  4
% 3.29/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.29/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/1.03  --bmc1_ucm_layered_model                none
% 3.29/1.03  --bmc1_ucm_max_lemma_size               10
% 3.29/1.03  
% 3.29/1.03  ------ AIG Options
% 3.29/1.03  
% 3.29/1.03  --aig_mode                              false
% 3.29/1.03  
% 3.29/1.03  ------ Instantiation Options
% 3.29/1.03  
% 3.29/1.03  --instantiation_flag                    true
% 3.29/1.03  --inst_sos_flag                         false
% 3.29/1.03  --inst_sos_phase                        true
% 3.29/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/1.03  --inst_lit_sel_side                     num_symb
% 3.29/1.03  --inst_solver_per_active                1400
% 3.29/1.03  --inst_solver_calls_frac                1.
% 3.29/1.03  --inst_passive_queue_type               priority_queues
% 3.29/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/1.03  --inst_passive_queues_freq              [25;2]
% 3.29/1.03  --inst_dismatching                      true
% 3.29/1.03  --inst_eager_unprocessed_to_passive     true
% 3.29/1.03  --inst_prop_sim_given                   true
% 3.29/1.03  --inst_prop_sim_new                     false
% 3.29/1.03  --inst_subs_new                         false
% 3.29/1.03  --inst_eq_res_simp                      false
% 3.29/1.03  --inst_subs_given                       false
% 3.29/1.03  --inst_orphan_elimination               true
% 3.29/1.03  --inst_learning_loop_flag               true
% 3.29/1.03  --inst_learning_start                   3000
% 3.29/1.03  --inst_learning_factor                  2
% 3.29/1.03  --inst_start_prop_sim_after_learn       3
% 3.29/1.03  --inst_sel_renew                        solver
% 3.29/1.03  --inst_lit_activity_flag                true
% 3.29/1.03  --inst_restr_to_given                   false
% 3.29/1.03  --inst_activity_threshold               500
% 3.29/1.03  --inst_out_proof                        true
% 3.29/1.03  
% 3.29/1.03  ------ Resolution Options
% 3.29/1.03  
% 3.29/1.03  --resolution_flag                       true
% 3.29/1.03  --res_lit_sel                           adaptive
% 3.29/1.03  --res_lit_sel_side                      none
% 3.29/1.03  --res_ordering                          kbo
% 3.29/1.03  --res_to_prop_solver                    active
% 3.29/1.03  --res_prop_simpl_new                    false
% 3.29/1.03  --res_prop_simpl_given                  true
% 3.29/1.03  --res_passive_queue_type                priority_queues
% 3.29/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/1.03  --res_passive_queues_freq               [15;5]
% 3.29/1.03  --res_forward_subs                      full
% 3.29/1.03  --res_backward_subs                     full
% 3.29/1.03  --res_forward_subs_resolution           true
% 3.29/1.03  --res_backward_subs_resolution          true
% 3.29/1.03  --res_orphan_elimination                true
% 3.29/1.03  --res_time_limit                        2.
% 3.29/1.03  --res_out_proof                         true
% 3.29/1.03  
% 3.29/1.03  ------ Superposition Options
% 3.29/1.03  
% 3.29/1.03  --superposition_flag                    true
% 3.29/1.03  --sup_passive_queue_type                priority_queues
% 3.29/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.29/1.03  --demod_completeness_check              fast
% 3.29/1.03  --demod_use_ground                      true
% 3.29/1.03  --sup_to_prop_solver                    passive
% 3.29/1.03  --sup_prop_simpl_new                    true
% 3.29/1.03  --sup_prop_simpl_given                  true
% 3.29/1.03  --sup_fun_splitting                     false
% 3.29/1.03  --sup_smt_interval                      50000
% 3.29/1.03  
% 3.29/1.03  ------ Superposition Simplification Setup
% 3.29/1.03  
% 3.29/1.03  --sup_indices_passive                   []
% 3.29/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.03  --sup_full_bw                           [BwDemod]
% 3.29/1.03  --sup_immed_triv                        [TrivRules]
% 3.29/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.03  --sup_immed_bw_main                     []
% 3.29/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.03  
% 3.29/1.03  ------ Combination Options
% 3.29/1.03  
% 3.29/1.03  --comb_res_mult                         3
% 3.29/1.03  --comb_sup_mult                         2
% 3.29/1.03  --comb_inst_mult                        10
% 3.29/1.03  
% 3.29/1.03  ------ Debug Options
% 3.29/1.03  
% 3.29/1.03  --dbg_backtrace                         false
% 3.29/1.03  --dbg_dump_prop_clauses                 false
% 3.29/1.03  --dbg_dump_prop_clauses_file            -
% 3.29/1.03  --dbg_out_stat                          false
% 3.29/1.03  ------ Parsing...
% 3.29/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/1.03  
% 3.29/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.29/1.03  
% 3.29/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/1.03  
% 3.29/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/1.03  ------ Proving...
% 3.29/1.03  ------ Problem Properties 
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  clauses                                 29
% 3.29/1.03  conjectures                             2
% 3.29/1.03  EPR                                     3
% 3.29/1.03  Horn                                    24
% 3.29/1.03  unary                                   12
% 3.29/1.03  binary                                  9
% 3.29/1.03  lits                                    56
% 3.29/1.03  lits eq                                 23
% 3.29/1.03  fd_pure                                 0
% 3.29/1.03  fd_pseudo                               0
% 3.29/1.03  fd_cond                                 0
% 3.29/1.03  fd_pseudo_cond                          6
% 3.29/1.03  AC symbols                              0
% 3.29/1.03  
% 3.29/1.03  ------ Schedule dynamic 5 is on 
% 3.29/1.03  
% 3.29/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  ------ 
% 3.29/1.03  Current options:
% 3.29/1.03  ------ 
% 3.29/1.03  
% 3.29/1.03  ------ Input Options
% 3.29/1.03  
% 3.29/1.03  --out_options                           all
% 3.29/1.03  --tptp_safe_out                         true
% 3.29/1.03  --problem_path                          ""
% 3.29/1.03  --include_path                          ""
% 3.29/1.03  --clausifier                            res/vclausify_rel
% 3.29/1.03  --clausifier_options                    --mode clausify
% 3.29/1.03  --stdin                                 false
% 3.29/1.03  --stats_out                             all
% 3.29/1.03  
% 3.29/1.03  ------ General Options
% 3.29/1.03  
% 3.29/1.03  --fof                                   false
% 3.29/1.03  --time_out_real                         305.
% 3.29/1.03  --time_out_virtual                      -1.
% 3.29/1.03  --symbol_type_check                     false
% 3.29/1.03  --clausify_out                          false
% 3.29/1.03  --sig_cnt_out                           false
% 3.29/1.03  --trig_cnt_out                          false
% 3.29/1.03  --trig_cnt_out_tolerance                1.
% 3.29/1.03  --trig_cnt_out_sk_spl                   false
% 3.29/1.03  --abstr_cl_out                          false
% 3.29/1.03  
% 3.29/1.03  ------ Global Options
% 3.29/1.03  
% 3.29/1.03  --schedule                              default
% 3.29/1.03  --add_important_lit                     false
% 3.29/1.03  --prop_solver_per_cl                    1000
% 3.29/1.03  --min_unsat_core                        false
% 3.29/1.03  --soft_assumptions                      false
% 3.29/1.03  --soft_lemma_size                       3
% 3.29/1.03  --prop_impl_unit_size                   0
% 3.29/1.03  --prop_impl_unit                        []
% 3.29/1.03  --share_sel_clauses                     true
% 3.29/1.03  --reset_solvers                         false
% 3.29/1.03  --bc_imp_inh                            [conj_cone]
% 3.29/1.03  --conj_cone_tolerance                   3.
% 3.29/1.03  --extra_neg_conj                        none
% 3.29/1.03  --large_theory_mode                     true
% 3.29/1.03  --prolific_symb_bound                   200
% 3.29/1.03  --lt_threshold                          2000
% 3.29/1.03  --clause_weak_htbl                      true
% 3.29/1.03  --gc_record_bc_elim                     false
% 3.29/1.03  
% 3.29/1.03  ------ Preprocessing Options
% 3.29/1.03  
% 3.29/1.03  --preprocessing_flag                    true
% 3.29/1.03  --time_out_prep_mult                    0.1
% 3.29/1.03  --splitting_mode                        input
% 3.29/1.03  --splitting_grd                         true
% 3.29/1.03  --splitting_cvd                         false
% 3.29/1.03  --splitting_cvd_svl                     false
% 3.29/1.03  --splitting_nvd                         32
% 3.29/1.03  --sub_typing                            true
% 3.29/1.03  --prep_gs_sim                           true
% 3.29/1.03  --prep_unflatten                        true
% 3.29/1.03  --prep_res_sim                          true
% 3.29/1.03  --prep_upred                            true
% 3.29/1.03  --prep_sem_filter                       exhaustive
% 3.29/1.03  --prep_sem_filter_out                   false
% 3.29/1.03  --pred_elim                             true
% 3.29/1.03  --res_sim_input                         true
% 3.29/1.03  --eq_ax_congr_red                       true
% 3.29/1.03  --pure_diseq_elim                       true
% 3.29/1.03  --brand_transform                       false
% 3.29/1.03  --non_eq_to_eq                          false
% 3.29/1.03  --prep_def_merge                        true
% 3.29/1.03  --prep_def_merge_prop_impl              false
% 3.29/1.03  --prep_def_merge_mbd                    true
% 3.29/1.03  --prep_def_merge_tr_red                 false
% 3.29/1.03  --prep_def_merge_tr_cl                  false
% 3.29/1.03  --smt_preprocessing                     true
% 3.29/1.03  --smt_ac_axioms                         fast
% 3.29/1.03  --preprocessed_out                      false
% 3.29/1.03  --preprocessed_stats                    false
% 3.29/1.03  
% 3.29/1.03  ------ Abstraction refinement Options
% 3.29/1.03  
% 3.29/1.03  --abstr_ref                             []
% 3.29/1.03  --abstr_ref_prep                        false
% 3.29/1.03  --abstr_ref_until_sat                   false
% 3.29/1.03  --abstr_ref_sig_restrict                funpre
% 3.29/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/1.03  --abstr_ref_under                       []
% 3.29/1.03  
% 3.29/1.03  ------ SAT Options
% 3.29/1.03  
% 3.29/1.03  --sat_mode                              false
% 3.29/1.03  --sat_fm_restart_options                ""
% 3.29/1.03  --sat_gr_def                            false
% 3.29/1.03  --sat_epr_types                         true
% 3.29/1.03  --sat_non_cyclic_types                  false
% 3.29/1.03  --sat_finite_models                     false
% 3.29/1.03  --sat_fm_lemmas                         false
% 3.29/1.03  --sat_fm_prep                           false
% 3.29/1.03  --sat_fm_uc_incr                        true
% 3.29/1.03  --sat_out_model                         small
% 3.29/1.03  --sat_out_clauses                       false
% 3.29/1.03  
% 3.29/1.03  ------ QBF Options
% 3.29/1.03  
% 3.29/1.03  --qbf_mode                              false
% 3.29/1.03  --qbf_elim_univ                         false
% 3.29/1.03  --qbf_dom_inst                          none
% 3.29/1.03  --qbf_dom_pre_inst                      false
% 3.29/1.03  --qbf_sk_in                             false
% 3.29/1.03  --qbf_pred_elim                         true
% 3.29/1.03  --qbf_split                             512
% 3.29/1.03  
% 3.29/1.03  ------ BMC1 Options
% 3.29/1.03  
% 3.29/1.03  --bmc1_incremental                      false
% 3.29/1.03  --bmc1_axioms                           reachable_all
% 3.29/1.03  --bmc1_min_bound                        0
% 3.29/1.03  --bmc1_max_bound                        -1
% 3.29/1.03  --bmc1_max_bound_default                -1
% 3.29/1.03  --bmc1_symbol_reachability              true
% 3.29/1.03  --bmc1_property_lemmas                  false
% 3.29/1.03  --bmc1_k_induction                      false
% 3.29/1.03  --bmc1_non_equiv_states                 false
% 3.29/1.03  --bmc1_deadlock                         false
% 3.29/1.03  --bmc1_ucm                              false
% 3.29/1.03  --bmc1_add_unsat_core                   none
% 3.29/1.03  --bmc1_unsat_core_children              false
% 3.29/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/1.03  --bmc1_out_stat                         full
% 3.29/1.03  --bmc1_ground_init                      false
% 3.29/1.03  --bmc1_pre_inst_next_state              false
% 3.29/1.03  --bmc1_pre_inst_state                   false
% 3.29/1.03  --bmc1_pre_inst_reach_state             false
% 3.29/1.03  --bmc1_out_unsat_core                   false
% 3.29/1.03  --bmc1_aig_witness_out                  false
% 3.29/1.03  --bmc1_verbose                          false
% 3.29/1.03  --bmc1_dump_clauses_tptp                false
% 3.29/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.29/1.03  --bmc1_dump_file                        -
% 3.29/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.29/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.29/1.03  --bmc1_ucm_extend_mode                  1
% 3.29/1.03  --bmc1_ucm_init_mode                    2
% 3.29/1.03  --bmc1_ucm_cone_mode                    none
% 3.29/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.29/1.03  --bmc1_ucm_relax_model                  4
% 3.29/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.29/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/1.03  --bmc1_ucm_layered_model                none
% 3.29/1.03  --bmc1_ucm_max_lemma_size               10
% 3.29/1.03  
% 3.29/1.03  ------ AIG Options
% 3.29/1.03  
% 3.29/1.03  --aig_mode                              false
% 3.29/1.03  
% 3.29/1.03  ------ Instantiation Options
% 3.29/1.03  
% 3.29/1.03  --instantiation_flag                    true
% 3.29/1.03  --inst_sos_flag                         false
% 3.29/1.03  --inst_sos_phase                        true
% 3.29/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/1.03  --inst_lit_sel_side                     none
% 3.29/1.03  --inst_solver_per_active                1400
% 3.29/1.03  --inst_solver_calls_frac                1.
% 3.29/1.03  --inst_passive_queue_type               priority_queues
% 3.29/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/1.03  --inst_passive_queues_freq              [25;2]
% 3.29/1.03  --inst_dismatching                      true
% 3.29/1.03  --inst_eager_unprocessed_to_passive     true
% 3.29/1.03  --inst_prop_sim_given                   true
% 3.29/1.03  --inst_prop_sim_new                     false
% 3.29/1.03  --inst_subs_new                         false
% 3.29/1.03  --inst_eq_res_simp                      false
% 3.29/1.03  --inst_subs_given                       false
% 3.29/1.03  --inst_orphan_elimination               true
% 3.29/1.03  --inst_learning_loop_flag               true
% 3.29/1.03  --inst_learning_start                   3000
% 3.29/1.03  --inst_learning_factor                  2
% 3.29/1.03  --inst_start_prop_sim_after_learn       3
% 3.29/1.03  --inst_sel_renew                        solver
% 3.29/1.03  --inst_lit_activity_flag                true
% 3.29/1.03  --inst_restr_to_given                   false
% 3.29/1.03  --inst_activity_threshold               500
% 3.29/1.03  --inst_out_proof                        true
% 3.29/1.03  
% 3.29/1.03  ------ Resolution Options
% 3.29/1.03  
% 3.29/1.03  --resolution_flag                       false
% 3.29/1.03  --res_lit_sel                           adaptive
% 3.29/1.03  --res_lit_sel_side                      none
% 3.29/1.03  --res_ordering                          kbo
% 3.29/1.03  --res_to_prop_solver                    active
% 3.29/1.03  --res_prop_simpl_new                    false
% 3.29/1.03  --res_prop_simpl_given                  true
% 3.29/1.03  --res_passive_queue_type                priority_queues
% 3.29/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/1.03  --res_passive_queues_freq               [15;5]
% 3.29/1.03  --res_forward_subs                      full
% 3.29/1.03  --res_backward_subs                     full
% 3.29/1.03  --res_forward_subs_resolution           true
% 3.29/1.03  --res_backward_subs_resolution          true
% 3.29/1.03  --res_orphan_elimination                true
% 3.29/1.03  --res_time_limit                        2.
% 3.29/1.03  --res_out_proof                         true
% 3.29/1.03  
% 3.29/1.03  ------ Superposition Options
% 3.29/1.03  
% 3.29/1.03  --superposition_flag                    true
% 3.29/1.03  --sup_passive_queue_type                priority_queues
% 3.29/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.29/1.03  --demod_completeness_check              fast
% 3.29/1.03  --demod_use_ground                      true
% 3.29/1.03  --sup_to_prop_solver                    passive
% 3.29/1.03  --sup_prop_simpl_new                    true
% 3.29/1.03  --sup_prop_simpl_given                  true
% 3.29/1.03  --sup_fun_splitting                     false
% 3.29/1.03  --sup_smt_interval                      50000
% 3.29/1.03  
% 3.29/1.03  ------ Superposition Simplification Setup
% 3.29/1.03  
% 3.29/1.03  --sup_indices_passive                   []
% 3.29/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.03  --sup_full_bw                           [BwDemod]
% 3.29/1.03  --sup_immed_triv                        [TrivRules]
% 3.29/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.03  --sup_immed_bw_main                     []
% 3.29/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.03  
% 3.29/1.03  ------ Combination Options
% 3.29/1.03  
% 3.29/1.03  --comb_res_mult                         3
% 3.29/1.03  --comb_sup_mult                         2
% 3.29/1.03  --comb_inst_mult                        10
% 3.29/1.03  
% 3.29/1.03  ------ Debug Options
% 3.29/1.03  
% 3.29/1.03  --dbg_backtrace                         false
% 3.29/1.03  --dbg_dump_prop_clauses                 false
% 3.29/1.03  --dbg_dump_prop_clauses_file            -
% 3.29/1.03  --dbg_out_stat                          false
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  ------ Proving...
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  % SZS status Theorem for theBenchmark.p
% 3.29/1.03  
% 3.29/1.03   Resolution empty clause
% 3.29/1.03  
% 3.29/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/1.03  
% 3.29/1.03  fof(f18,conjecture,(
% 3.29/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f19,negated_conjecture,(
% 3.29/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.29/1.03    inference(negated_conjecture,[],[f18])).
% 3.29/1.03  
% 3.29/1.03  fof(f26,plain,(
% 3.29/1.03    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 3.29/1.03    inference(ennf_transformation,[],[f19])).
% 3.29/1.03  
% 3.29/1.03  fof(f27,plain,(
% 3.29/1.03    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.29/1.03    inference(flattening,[],[f26])).
% 3.29/1.03  
% 3.29/1.03  fof(f51,plain,(
% 3.29/1.03    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK6 != X0 & r1_tarski(X0,sK6) & v1_zfmisc_1(sK6) & ~v1_xboole_0(sK6))) )),
% 3.29/1.03    introduced(choice_axiom,[])).
% 3.29/1.03  
% 3.29/1.03  fof(f50,plain,(
% 3.29/1.03    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK5 != X1 & r1_tarski(sK5,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK5))),
% 3.29/1.03    introduced(choice_axiom,[])).
% 3.29/1.03  
% 3.29/1.03  fof(f52,plain,(
% 3.29/1.03    (sK5 != sK6 & r1_tarski(sK5,sK6) & v1_zfmisc_1(sK6) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)),
% 3.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f51,f50])).
% 3.29/1.03  
% 3.29/1.03  fof(f87,plain,(
% 3.29/1.03    r1_tarski(sK5,sK6)),
% 3.29/1.03    inference(cnf_transformation,[],[f52])).
% 3.29/1.03  
% 3.29/1.03  fof(f4,axiom,(
% 3.29/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f41,plain,(
% 3.29/1.03    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.29/1.03    inference(nnf_transformation,[],[f4])).
% 3.29/1.03  
% 3.29/1.03  fof(f65,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f41])).
% 3.29/1.03  
% 3.29/1.03  fof(f12,axiom,(
% 3.29/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f76,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.29/1.03    inference(cnf_transformation,[],[f12])).
% 3.29/1.03  
% 3.29/1.03  fof(f8,axiom,(
% 3.29/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f69,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.29/1.03    inference(cnf_transformation,[],[f8])).
% 3.29/1.03  
% 3.29/1.03  fof(f101,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.29/1.03    inference(definition_unfolding,[],[f76,f69])).
% 3.29/1.03  
% 3.29/1.03  fof(f5,axiom,(
% 3.29/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f66,plain,(
% 3.29/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.29/1.03    inference(cnf_transformation,[],[f5])).
% 3.29/1.03  
% 3.29/1.03  fof(f95,plain,(
% 3.29/1.03    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 3.29/1.03    inference(definition_unfolding,[],[f66,f69])).
% 3.29/1.03  
% 3.29/1.03  fof(f7,axiom,(
% 3.29/1.03    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f68,plain,(
% 3.29/1.03    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.29/1.03    inference(cnf_transformation,[],[f7])).
% 3.29/1.03  
% 3.29/1.03  fof(f13,axiom,(
% 3.29/1.03    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f22,plain,(
% 3.29/1.03    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 3.29/1.03    inference(ennf_transformation,[],[f13])).
% 3.29/1.03  
% 3.29/1.03  fof(f77,plain,(
% 3.29/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f22])).
% 3.29/1.03  
% 3.29/1.03  fof(f11,axiom,(
% 3.29/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f75,plain,(
% 3.29/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f11])).
% 3.29/1.03  
% 3.29/1.03  fof(f102,plain,(
% 3.29/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k5_xboole_0(X1,k4_xboole_0(X2,X1)) != k2_tarski(X0,X0)) )),
% 3.29/1.03    inference(definition_unfolding,[],[f77,f69,f75])).
% 3.29/1.03  
% 3.29/1.03  fof(f1,axiom,(
% 3.29/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f28,plain,(
% 3.29/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.29/1.03    inference(nnf_transformation,[],[f1])).
% 3.29/1.03  
% 3.29/1.03  fof(f29,plain,(
% 3.29/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.29/1.03    inference(rectify,[],[f28])).
% 3.29/1.03  
% 3.29/1.03  fof(f30,plain,(
% 3.29/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.29/1.03    introduced(choice_axiom,[])).
% 3.29/1.03  
% 3.29/1.03  fof(f31,plain,(
% 3.29/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.29/1.03  
% 3.29/1.03  fof(f54,plain,(
% 3.29/1.03    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f31])).
% 3.29/1.03  
% 3.29/1.03  fof(f84,plain,(
% 3.29/1.03    ~v1_xboole_0(sK5)),
% 3.29/1.03    inference(cnf_transformation,[],[f52])).
% 3.29/1.03  
% 3.29/1.03  fof(f10,axiom,(
% 3.29/1.03    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f42,plain,(
% 3.29/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.29/1.03    inference(nnf_transformation,[],[f10])).
% 3.29/1.03  
% 3.29/1.03  fof(f43,plain,(
% 3.29/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/1.03    inference(rectify,[],[f42])).
% 3.29/1.03  
% 3.29/1.03  fof(f44,plain,(
% 3.29/1.03    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.29/1.03    introduced(choice_axiom,[])).
% 3.29/1.03  
% 3.29/1.03  fof(f45,plain,(
% 3.29/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 3.29/1.03  
% 3.29/1.03  fof(f73,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f45])).
% 3.29/1.03  
% 3.29/1.03  fof(f98,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 3.29/1.03    inference(definition_unfolding,[],[f73,f75])).
% 3.29/1.03  
% 3.29/1.03  fof(f2,axiom,(
% 3.29/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f20,plain,(
% 3.29/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.29/1.03    inference(ennf_transformation,[],[f2])).
% 3.29/1.03  
% 3.29/1.03  fof(f32,plain,(
% 3.29/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.29/1.03    inference(nnf_transformation,[],[f20])).
% 3.29/1.03  
% 3.29/1.03  fof(f33,plain,(
% 3.29/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.29/1.03    inference(rectify,[],[f32])).
% 3.29/1.03  
% 3.29/1.03  fof(f34,plain,(
% 3.29/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.29/1.03    introduced(choice_axiom,[])).
% 3.29/1.03  
% 3.29/1.03  fof(f35,plain,(
% 3.29/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.29/1.03  
% 3.29/1.03  fof(f55,plain,(
% 3.29/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f35])).
% 3.29/1.03  
% 3.29/1.03  fof(f85,plain,(
% 3.29/1.03    ~v1_xboole_0(sK6)),
% 3.29/1.03    inference(cnf_transformation,[],[f52])).
% 3.29/1.03  
% 3.29/1.03  fof(f16,axiom,(
% 3.29/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f23,plain,(
% 3.29/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.29/1.03    inference(ennf_transformation,[],[f16])).
% 3.29/1.03  
% 3.29/1.03  fof(f24,plain,(
% 3.29/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.29/1.03    inference(flattening,[],[f23])).
% 3.29/1.03  
% 3.29/1.03  fof(f80,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f24])).
% 3.29/1.03  
% 3.29/1.03  fof(f104,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.29/1.03    inference(definition_unfolding,[],[f80,f75])).
% 3.29/1.03  
% 3.29/1.03  fof(f17,axiom,(
% 3.29/1.03    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 3.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.03  
% 3.29/1.03  fof(f25,plain,(
% 3.29/1.03    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 3.29/1.03    inference(ennf_transformation,[],[f17])).
% 3.29/1.03  
% 3.29/1.03  fof(f46,plain,(
% 3.29/1.03    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.29/1.03    inference(nnf_transformation,[],[f25])).
% 3.29/1.03  
% 3.29/1.03  fof(f47,plain,(
% 3.29/1.03    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.29/1.03    inference(rectify,[],[f46])).
% 3.29/1.03  
% 3.29/1.03  fof(f48,plain,(
% 3.29/1.03    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)))),
% 3.29/1.03    introduced(choice_axiom,[])).
% 3.29/1.03  
% 3.29/1.03  fof(f49,plain,(
% 3.29/1.03    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK4(X0)) = X0 & m1_subset_1(sK4(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 3.29/1.03  
% 3.29/1.03  fof(f81,plain,(
% 3.29/1.03    ( ! [X0] : (m1_subset_1(sK4(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f49])).
% 3.29/1.03  
% 3.29/1.03  fof(f86,plain,(
% 3.29/1.03    v1_zfmisc_1(sK6)),
% 3.29/1.03    inference(cnf_transformation,[],[f52])).
% 3.29/1.03  
% 3.29/1.03  fof(f82,plain,(
% 3.29/1.03    ( ! [X0] : (k6_domain_1(X0,sK4(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f49])).
% 3.29/1.03  
% 3.29/1.03  fof(f71,plain,(
% 3.29/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.29/1.03    inference(cnf_transformation,[],[f45])).
% 3.29/1.03  
% 3.29/1.03  fof(f100,plain,(
% 3.29/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 3.29/1.03    inference(definition_unfolding,[],[f71,f75])).
% 3.29/1.03  
% 3.29/1.03  fof(f110,plain,(
% 3.29/1.03    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 3.29/1.03    inference(equality_resolution,[],[f100])).
% 3.29/1.03  
% 3.29/1.03  fof(f74,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 3.29/1.03    inference(cnf_transformation,[],[f45])).
% 3.29/1.03  
% 3.29/1.03  fof(f97,plain,(
% 3.29/1.03    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 3.29/1.03    inference(definition_unfolding,[],[f74,f75])).
% 3.29/1.03  
% 3.29/1.03  fof(f88,plain,(
% 3.29/1.03    sK5 != sK6),
% 3.29/1.03    inference(cnf_transformation,[],[f52])).
% 3.29/1.03  
% 3.29/1.03  cnf(c_29,negated_conjecture,
% 3.29/1.03      ( r1_tarski(sK5,sK6) ),
% 3.29/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1372,plain,
% 3.29/1.03      ( r1_tarski(sK5,sK6) = iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_11,plain,
% 3.29/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.29/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1379,plain,
% 3.29/1.03      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_3001,plain,
% 3.29/1.03      ( k4_xboole_0(sK5,sK6) = k1_xboole_0 ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_1372,c_1379]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_21,plain,
% 3.29/1.03      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 3.29/1.03      inference(cnf_transformation,[],[f101]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_3211,plain,
% 3.29/1.03      ( k3_tarski(k2_tarski(sK6,sK5)) = k5_xboole_0(sK6,k1_xboole_0) ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_3001,c_21]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_13,plain,
% 3.29/1.03      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.29/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_15,plain,
% 3.29/1.03      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.29/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1405,plain,
% 3.29/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.29/1.03      inference(light_normalisation,[status(thm)],[c_13,c_15]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_3213,plain,
% 3.29/1.03      ( k3_tarski(k2_tarski(sK6,sK5)) = sK6 ),
% 3.29/1.03      inference(demodulation,[status(thm)],[c_3211,c_1405]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_22,plain,
% 3.29/1.03      ( X0 = X1
% 3.29/1.03      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != k2_tarski(X2,X2)
% 3.29/1.03      | k1_xboole_0 = X1
% 3.29/1.03      | k1_xboole_0 = X0 ),
% 3.29/1.03      inference(cnf_transformation,[],[f102]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1470,plain,
% 3.29/1.03      ( X0 = X1
% 3.29/1.03      | k3_tarski(k2_tarski(X1,X0)) != k2_tarski(X2,X2)
% 3.29/1.03      | k1_xboole_0 = X0
% 3.29/1.03      | k1_xboole_0 = X1 ),
% 3.29/1.03      inference(light_normalisation,[status(thm)],[c_22,c_21]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_5599,plain,
% 3.29/1.03      ( k2_tarski(X0,X0) != sK6
% 3.29/1.03      | sK6 = sK5
% 3.29/1.03      | sK6 = k1_xboole_0
% 3.29/1.03      | sK5 = k1_xboole_0 ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_3213,c_1470]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_0,plain,
% 3.29/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.29/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_32,negated_conjecture,
% 3.29/1.03      ( ~ v1_xboole_0(sK5) ),
% 3.29/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_424,plain,
% 3.29/1.03      ( r2_hidden(sK0(X0),X0) | sK5 != X0 ),
% 3.29/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_32]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_425,plain,
% 3.29/1.03      ( r2_hidden(sK0(sK5),sK5) ),
% 3.29/1.03      inference(unflattening,[status(thm)],[c_424]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_426,plain,
% 3.29/1.03      ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_18,plain,
% 3.29/1.03      ( r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) = X0 | k2_tarski(X0,X0) = X1 ),
% 3.29/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1375,plain,
% 3.29/1.03      ( sK3(X0,X1) = X0
% 3.29/1.03      | k2_tarski(X0,X0) = X1
% 3.29/1.03      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_4,plain,
% 3.29/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.29/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1386,plain,
% 3.29/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.29/1.03      | r2_hidden(X2,X0) != iProver_top
% 3.29/1.03      | r2_hidden(X2,X1) = iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_3890,plain,
% 3.29/1.03      ( r2_hidden(X0,sK6) = iProver_top | r2_hidden(X0,sK5) != iProver_top ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_1372,c_1386]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_5016,plain,
% 3.29/1.03      ( sK3(X0,sK5) = X0
% 3.29/1.03      | k2_tarski(X0,X0) = sK5
% 3.29/1.03      | r2_hidden(sK3(X0,sK5),sK6) = iProver_top ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_1375,c_3890]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1369,plain,
% 3.29/1.03      ( r2_hidden(sK0(sK5),sK5) = iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_4227,plain,
% 3.29/1.03      ( r2_hidden(sK0(sK5),sK6) = iProver_top ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_1369,c_3890]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_31,negated_conjecture,
% 3.29/1.03      ( ~ v1_xboole_0(sK6) ),
% 3.29/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_417,plain,
% 3.29/1.03      ( r2_hidden(sK0(X0),X0) | sK6 != X0 ),
% 3.29/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_31]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_418,plain,
% 3.29/1.03      ( r2_hidden(sK0(sK6),sK6) ),
% 3.29/1.03      inference(unflattening,[status(thm)],[c_417]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1370,plain,
% 3.29/1.03      ( r2_hidden(sK0(sK6),sK6) = iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_24,plain,
% 3.29/1.03      ( ~ m1_subset_1(X0,X1)
% 3.29/1.03      | v1_xboole_0(X1)
% 3.29/1.03      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.29/1.03      inference(cnf_transformation,[],[f104]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_27,plain,
% 3.29/1.03      ( m1_subset_1(sK4(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 3.29/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_368,plain,
% 3.29/1.03      ( ~ v1_zfmisc_1(X0)
% 3.29/1.03      | v1_xboole_0(X1)
% 3.29/1.03      | v1_xboole_0(X0)
% 3.29/1.03      | X0 != X1
% 3.29/1.03      | k6_domain_1(X1,X2) = k2_tarski(X2,X2)
% 3.29/1.03      | sK4(X0) != X2 ),
% 3.29/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_369,plain,
% 3.29/1.03      ( ~ v1_zfmisc_1(X0)
% 3.29/1.03      | v1_xboole_0(X0)
% 3.29/1.03      | k6_domain_1(X0,sK4(X0)) = k2_tarski(sK4(X0),sK4(X0)) ),
% 3.29/1.03      inference(unflattening,[status(thm)],[c_368]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_30,negated_conjecture,
% 3.29/1.03      ( v1_zfmisc_1(sK6) ),
% 3.29/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_387,plain,
% 3.29/1.03      ( v1_xboole_0(X0)
% 3.29/1.03      | k2_tarski(sK4(X0),sK4(X0)) = k6_domain_1(X0,sK4(X0))
% 3.29/1.03      | sK6 != X0 ),
% 3.29/1.03      inference(resolution_lifted,[status(thm)],[c_369,c_30]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_388,plain,
% 3.29/1.03      ( v1_xboole_0(sK6)
% 3.29/1.03      | k2_tarski(sK4(sK6),sK4(sK6)) = k6_domain_1(sK6,sK4(sK6)) ),
% 3.29/1.03      inference(unflattening,[status(thm)],[c_387]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_390,plain,
% 3.29/1.03      ( k2_tarski(sK4(sK6),sK4(sK6)) = k6_domain_1(sK6,sK4(sK6)) ),
% 3.29/1.03      inference(global_propositional_subsumption,[status(thm)],[c_388,c_31]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_26,plain,
% 3.29/1.03      ( ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK4(X0)) = X0 ),
% 3.29/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_395,plain,
% 3.29/1.03      ( v1_xboole_0(X0) | k6_domain_1(X0,sK4(X0)) = X0 | sK6 != X0 ),
% 3.29/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_396,plain,
% 3.29/1.03      ( v1_xboole_0(sK6) | k6_domain_1(sK6,sK4(sK6)) = sK6 ),
% 3.29/1.03      inference(unflattening,[status(thm)],[c_395]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_398,plain,
% 3.29/1.03      ( k6_domain_1(sK6,sK4(sK6)) = sK6 ),
% 3.29/1.03      inference(global_propositional_subsumption,[status(thm)],[c_396,c_31]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1408,plain,
% 3.29/1.03      ( k2_tarski(sK4(sK6),sK4(sK6)) = sK6 ),
% 3.29/1.03      inference(light_normalisation,[status(thm)],[c_390,c_398]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_20,plain,
% 3.29/1.03      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 3.29/1.03      inference(cnf_transformation,[],[f110]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1373,plain,
% 3.29/1.03      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_2990,plain,
% 3.29/1.03      ( sK4(sK6) = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_1408,c_1373]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_3218,plain,
% 3.29/1.03      ( sK4(sK6) = sK0(sK6) ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_1370,c_2990]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_3221,plain,
% 3.29/1.03      ( sK0(sK6) = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 3.29/1.03      inference(demodulation,[status(thm)],[c_3218,c_2990]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_4240,plain,
% 3.29/1.03      ( sK0(sK5) = sK0(sK6) ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_4227,c_3221]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_4384,plain,
% 3.29/1.03      ( sK0(sK5) = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 3.29/1.03      inference(demodulation,[status(thm)],[c_4240,c_3221]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_6249,plain,
% 3.29/1.03      ( sK3(X0,sK5) = X0 | sK3(X0,sK5) = sK0(sK5) | k2_tarski(X0,X0) = sK5 ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_5016,c_4384]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_3604,plain,
% 3.29/1.03      ( k2_tarski(sK0(sK6),sK0(sK6)) = sK6 ),
% 3.29/1.03      inference(demodulation,[status(thm)],[c_3218,c_1408]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_4385,plain,
% 3.29/1.03      ( k2_tarski(sK0(sK5),sK0(sK5)) = sK6 ),
% 3.29/1.03      inference(demodulation,[status(thm)],[c_4240,c_3604]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_6282,plain,
% 3.29/1.03      ( sK3(sK0(sK5),sK5) = sK0(sK5) | sK6 = sK5 ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_6249,c_4385]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_17,plain,
% 3.29/1.03      ( ~ r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) != X0 | k2_tarski(X0,X0) = X1 ),
% 3.29/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_1376,plain,
% 3.29/1.03      ( sK3(X0,X1) != X0
% 3.29/1.03      | k2_tarski(X0,X0) = X1
% 3.29/1.03      | r2_hidden(sK3(X0,X1),X1) != iProver_top ),
% 3.29/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_6938,plain,
% 3.29/1.03      ( k2_tarski(sK0(sK5),sK0(sK5)) = sK5
% 3.29/1.03      | sK6 = sK5
% 3.29/1.03      | r2_hidden(sK3(sK0(sK5),sK5),sK5) != iProver_top ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_6282,c_1376]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_6944,plain,
% 3.29/1.03      ( sK6 = sK5 | r2_hidden(sK3(sK0(sK5),sK5),sK5) != iProver_top ),
% 3.29/1.03      inference(demodulation,[status(thm)],[c_6938,c_4385]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_6954,plain,
% 3.29/1.03      ( sK6 = sK5 | r2_hidden(sK0(sK5),sK5) != iProver_top ),
% 3.29/1.03      inference(superposition,[status(thm)],[c_6282,c_6944]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_19425,plain,
% 3.29/1.03      ( sK6 = sK5 ),
% 3.29/1.03      inference(global_propositional_subsumption,
% 3.29/1.03                [status(thm)],
% 3.29/1.03                [c_5599,c_426,c_6954]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_28,negated_conjecture,
% 3.29/1.03      ( sK5 != sK6 ),
% 3.29/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_19481,plain,
% 3.29/1.03      ( sK5 != sK5 ),
% 3.29/1.03      inference(demodulation,[status(thm)],[c_19425,c_28]) ).
% 3.29/1.03  
% 3.29/1.03  cnf(c_19482,plain,
% 3.29/1.03      ( $false ),
% 3.29/1.03      inference(equality_resolution_simp,[status(thm)],[c_19481]) ).
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/1.03  
% 3.29/1.03  ------                               Statistics
% 3.29/1.03  
% 3.29/1.03  ------ General
% 3.29/1.03  
% 3.29/1.03  abstr_ref_over_cycles:                  0
% 3.29/1.03  abstr_ref_under_cycles:                 0
% 3.29/1.03  gc_basic_clause_elim:                   0
% 3.29/1.03  forced_gc_time:                         0
% 3.29/1.03  parsing_time:                           0.009
% 3.29/1.03  unif_index_cands_time:                  0.
% 3.29/1.03  unif_index_add_time:                    0.
% 3.29/1.03  orderings_time:                         0.
% 3.29/1.03  out_proof_time:                         0.01
% 3.29/1.03  total_time:                             0.422
% 3.29/1.03  num_of_symbols:                         50
% 3.29/1.03  num_of_terms:                           18921
% 3.29/1.03  
% 3.29/1.03  ------ Preprocessing
% 3.29/1.03  
% 3.29/1.03  num_of_splits:                          0
% 3.29/1.03  num_of_split_atoms:                     0
% 3.29/1.03  num_of_reused_defs:                     0
% 3.29/1.03  num_eq_ax_congr_red:                    27
% 3.29/1.03  num_of_sem_filtered_clauses:            1
% 3.29/1.03  num_of_subtypes:                        0
% 3.29/1.03  monotx_restored_types:                  0
% 3.29/1.03  sat_num_of_epr_types:                   0
% 3.29/1.03  sat_num_of_non_cyclic_types:            0
% 3.29/1.03  sat_guarded_non_collapsed_types:        0
% 3.29/1.03  num_pure_diseq_elim:                    0
% 3.29/1.03  simp_replaced_by:                       0
% 3.29/1.03  res_preprocessed:                       145
% 3.29/1.03  prep_upred:                             0
% 3.29/1.03  prep_unflattend:                        21
% 3.29/1.03  smt_new_axioms:                         0
% 3.29/1.03  pred_elim_cands:                        2
% 3.29/1.03  pred_elim:                              3
% 3.29/1.03  pred_elim_cl:                           4
% 3.29/1.03  pred_elim_cycles:                       5
% 3.29/1.03  merged_defs:                            8
% 3.29/1.03  merged_defs_ncl:                        0
% 3.29/1.03  bin_hyper_res:                          8
% 3.29/1.03  prep_cycles:                            4
% 3.29/1.03  pred_elim_time:                         0.003
% 3.29/1.03  splitting_time:                         0.
% 3.29/1.03  sem_filter_time:                        0.
% 3.29/1.03  monotx_time:                            0.
% 3.29/1.03  subtype_inf_time:                       0.
% 3.29/1.03  
% 3.29/1.03  ------ Problem properties
% 3.29/1.03  
% 3.29/1.03  clauses:                                29
% 3.29/1.03  conjectures:                            2
% 3.29/1.03  epr:                                    3
% 3.29/1.03  horn:                                   24
% 3.29/1.03  ground:                                 6
% 3.29/1.03  unary:                                  12
% 3.29/1.03  binary:                                 9
% 3.29/1.03  lits:                                   56
% 3.29/1.03  lits_eq:                                23
% 3.29/1.03  fd_pure:                                0
% 3.29/1.03  fd_pseudo:                              0
% 3.29/1.03  fd_cond:                                0
% 3.29/1.03  fd_pseudo_cond:                         6
% 3.29/1.03  ac_symbols:                             0
% 3.29/1.03  
% 3.29/1.03  ------ Propositional Solver
% 3.29/1.03  
% 3.29/1.03  prop_solver_calls:                      28
% 3.29/1.03  prop_fast_solver_calls:                 899
% 3.29/1.03  smt_solver_calls:                       0
% 3.29/1.03  smt_fast_solver_calls:                  0
% 3.29/1.03  prop_num_of_clauses:                    8161
% 3.29/1.03  prop_preprocess_simplified:             16190
% 3.29/1.03  prop_fo_subsumed:                       5
% 3.29/1.03  prop_solver_time:                       0.
% 3.29/1.03  smt_solver_time:                        0.
% 3.29/1.03  smt_fast_solver_time:                   0.
% 3.29/1.03  prop_fast_solver_time:                  0.
% 3.29/1.03  prop_unsat_core_time:                   0.
% 3.29/1.03  
% 3.29/1.03  ------ QBF
% 3.29/1.03  
% 3.29/1.03  qbf_q_res:                              0
% 3.29/1.03  qbf_num_tautologies:                    0
% 3.29/1.03  qbf_prep_cycles:                        0
% 3.29/1.03  
% 3.29/1.03  ------ BMC1
% 3.29/1.03  
% 3.29/1.03  bmc1_current_bound:                     -1
% 3.29/1.03  bmc1_last_solved_bound:                 -1
% 3.29/1.03  bmc1_unsat_core_size:                   -1
% 3.29/1.03  bmc1_unsat_core_parents_size:           -1
% 3.29/1.03  bmc1_merge_next_fun:                    0
% 3.29/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.29/1.03  
% 3.29/1.03  ------ Instantiation
% 3.29/1.03  
% 3.29/1.03  inst_num_of_clauses:                    2452
% 3.29/1.03  inst_num_in_passive:                    975
% 3.29/1.03  inst_num_in_active:                     520
% 3.29/1.03  inst_num_in_unprocessed:                958
% 3.29/1.03  inst_num_of_loops:                      620
% 3.29/1.03  inst_num_of_learning_restarts:          0
% 3.29/1.03  inst_num_moves_active_passive:          99
% 3.29/1.03  inst_lit_activity:                      0
% 3.29/1.03  inst_lit_activity_moves:                0
% 3.29/1.03  inst_num_tautologies:                   0
% 3.29/1.03  inst_num_prop_implied:                  0
% 3.29/1.03  inst_num_existing_simplified:           0
% 3.29/1.03  inst_num_eq_res_simplified:             0
% 3.29/1.03  inst_num_child_elim:                    0
% 3.29/1.03  inst_num_of_dismatching_blockings:      1779
% 3.29/1.03  inst_num_of_non_proper_insts:           2433
% 3.29/1.03  inst_num_of_duplicates:                 0
% 3.29/1.03  inst_inst_num_from_inst_to_res:         0
% 3.29/1.03  inst_dismatching_checking_time:         0.
% 3.29/1.03  
% 3.29/1.03  ------ Resolution
% 3.29/1.03  
% 3.29/1.03  res_num_of_clauses:                     0
% 3.29/1.03  res_num_in_passive:                     0
% 3.29/1.03  res_num_in_active:                      0
% 3.29/1.03  res_num_of_loops:                       149
% 3.29/1.03  res_forward_subset_subsumed:            297
% 3.29/1.03  res_backward_subset_subsumed:           2
% 3.29/1.03  res_forward_subsumed:                   0
% 3.29/1.03  res_backward_subsumed:                  0
% 3.29/1.03  res_forward_subsumption_resolution:     0
% 3.29/1.03  res_backward_subsumption_resolution:    0
% 3.29/1.03  res_clause_to_clause_subsumption:       1776
% 3.29/1.03  res_orphan_elimination:                 0
% 3.29/1.03  res_tautology_del:                      54
% 3.29/1.03  res_num_eq_res_simplified:              0
% 3.29/1.03  res_num_sel_changes:                    0
% 3.29/1.03  res_moves_from_active_to_pass:          0
% 3.29/1.03  
% 3.29/1.03  ------ Superposition
% 3.29/1.03  
% 3.29/1.03  sup_time_total:                         0.
% 3.29/1.03  sup_time_generating:                    0.
% 3.29/1.03  sup_time_sim_full:                      0.
% 3.29/1.03  sup_time_sim_immed:                     0.
% 3.29/1.03  
% 3.29/1.03  sup_num_of_clauses:                     273
% 3.29/1.03  sup_num_in_active:                      57
% 3.29/1.03  sup_num_in_passive:                     216
% 3.29/1.03  sup_num_of_loops:                       122
% 3.29/1.03  sup_fw_superposition:                   302
% 3.29/1.03  sup_bw_superposition:                   339
% 3.29/1.03  sup_immediate_simplified:               133
% 3.29/1.03  sup_given_eliminated:                   1
% 3.29/1.03  comparisons_done:                       0
% 3.29/1.03  comparisons_avoided:                    38
% 3.29/1.03  
% 3.29/1.03  ------ Simplifications
% 3.29/1.03  
% 3.29/1.03  
% 3.29/1.03  sim_fw_subset_subsumed:                 67
% 3.29/1.03  sim_bw_subset_subsumed:                 4
% 3.29/1.03  sim_fw_subsumed:                        32
% 3.29/1.03  sim_bw_subsumed:                        0
% 3.29/1.03  sim_fw_subsumption_res:                 6
% 3.29/1.03  sim_bw_subsumption_res:                 0
% 3.29/1.03  sim_tautology_del:                      16
% 3.29/1.03  sim_eq_tautology_del:                   15
% 3.29/1.03  sim_eq_res_simp:                        6
% 3.29/1.03  sim_fw_demodulated:                     14
% 3.29/1.03  sim_bw_demodulated:                     63
% 3.29/1.03  sim_light_normalised:                   27
% 3.29/1.03  sim_joinable_taut:                      0
% 3.29/1.03  sim_joinable_simp:                      0
% 3.29/1.03  sim_ac_normalised:                      0
% 3.29/1.03  sim_smt_subsumption:                    0
% 3.29/1.03  
%------------------------------------------------------------------------------

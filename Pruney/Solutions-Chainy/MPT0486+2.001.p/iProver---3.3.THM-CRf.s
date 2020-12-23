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
% DateTime   : Thu Dec  3 11:44:38 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 440 expanded)
%              Number of clauses        :   27 (  31 expanded)
%              Number of leaves         :   19 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 ( 588 expanded)
%              Number of equality atoms :  134 ( 489 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f133,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f108,f109])).

fof(f145,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f107,f144])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f106,f145])).

fof(f147,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f105,f146])).

fof(f148,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f104,f147])).

fof(f149,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f133,f148])).

fof(f151,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f92,f149])).

fof(f158,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f95,f151])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f77])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f78])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK7(X0,X1) != sK8(X0,X1)
          | ~ r2_hidden(sK7(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
        & ( ( sK7(X0,X1) = sK8(X0,X1)
            & r2_hidden(sK7(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK7(X0,X1) != sK8(X0,X1)
              | ~ r2_hidden(sK7(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
            & ( ( sK7(X0,X1) = sK8(X0,X1)
                & r2_hidden(sK7(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f79,f80])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X0)
      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f152,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f103,f148])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f127,f151,f152])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f123,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f171,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f123,f151,f152,f152,f152])).

fof(f186,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f171])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f29])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f125,f151,f148,f152,f152])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f39])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK9(X0)
        & r2_hidden(sK9(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK9(X0)
        & r2_hidden(sK9(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f57,f82])).

fof(f141,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK9(X0),X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f40,conjecture,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,negated_conjecture,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f40])).

fof(f44,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f41])).

fof(f143,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f158])).

cnf(c_28034,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_28024,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_28025,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28024])).

cnf(c_43,plain,
    ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
    | r2_hidden(sK7(X0,X1),X0)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_27696,plain,
    ( k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) = iProver_top
    | r2_hidden(sK7(X0,X1),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_35,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
    inference(cnf_transformation,[],[f175])).

cnf(c_27699,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_27907,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_27699])).

cnf(c_27974,plain,
    ( k6_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK7(X0,k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27696,c_27907])).

cnf(c_27990,plain,
    ( r2_hidden(sK7(X0,k1_xboole_0),X0)
    | ~ v1_relat_1(k1_xboole_0)
    | k6_relat_1(X0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27974])).

cnf(c_27992,plain,
    ( r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27990])).

cnf(c_27945,plain,
    ( ~ r2_hidden(sK7(X0,X1),X0)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1))))) != X0 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_27952,plain,
    ( ~ r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27945])).

cnf(c_27821,plain,
    ( ~ r2_hidden(sK9(X0),X0)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0))))) != X0 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_27823,plain,
    ( ~ r2_hidden(sK9(k1_xboole_0),k1_xboole_0)
    | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27821])).

cnf(c_628,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3976,plain,
    ( k6_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_3977,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3976])).

cnf(c_31,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f186])).

cnf(c_87,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_32,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_86,plain,
    ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_48,plain,
    ( r2_hidden(sK9(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_51,plain,
    ( r2_hidden(sK9(k1_xboole_0),k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_49,negated_conjecture,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f143])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28034,c_28025,c_27992,c_27952,c_27823,c_3977,c_87,c_86,c_51,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.61/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.48  
% 7.61/1.48  ------  iProver source info
% 7.61/1.48  
% 7.61/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.48  git: non_committed_changes: false
% 7.61/1.48  git: last_make_outside_of_git: false
% 7.61/1.48  
% 7.61/1.48  ------ 
% 7.61/1.48  ------ Parsing...
% 7.61/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  ------ Proving...
% 7.61/1.48  ------ Problem Properties 
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  clauses                                 49
% 7.61/1.48  conjectures                             1
% 7.61/1.48  EPR                                     2
% 7.61/1.48  Horn                                    38
% 7.61/1.48  unary                                   18
% 7.61/1.48  binary                                  20
% 7.61/1.48  lits                                    96
% 7.61/1.48  lits eq                                 48
% 7.61/1.48  fd_pure                                 0
% 7.61/1.48  fd_pseudo                               0
% 7.61/1.48  fd_cond                                 1
% 7.61/1.48  fd_pseudo_cond                          10
% 7.61/1.48  AC symbols                              1
% 7.61/1.48  
% 7.61/1.48  ------ Input Options Time Limit: Unbounded
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing...
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.61/1.48  Current options:
% 7.61/1.48  ------ 
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing...
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  % SZS status Theorem for theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  fof(f10,axiom,(
% 7.61/1.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f95,plain,(
% 7.61/1.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f10])).
% 7.61/1.48  
% 7.61/1.48  fof(f7,axiom,(
% 7.61/1.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f92,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f7])).
% 7.61/1.48  
% 7.61/1.48  fof(f36,axiom,(
% 7.61/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f133,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f16,axiom,(
% 7.61/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f104,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f16])).
% 7.61/1.48  
% 7.61/1.48  fof(f17,axiom,(
% 7.61/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f105,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f17])).
% 7.61/1.48  
% 7.61/1.48  fof(f18,axiom,(
% 7.61/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f106,plain,(
% 7.61/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f18])).
% 7.61/1.48  
% 7.61/1.48  fof(f19,axiom,(
% 7.61/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f107,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f19])).
% 7.61/1.48  
% 7.61/1.48  fof(f20,axiom,(
% 7.61/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f108,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f20])).
% 7.61/1.48  
% 7.61/1.48  fof(f21,axiom,(
% 7.61/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f109,plain,(
% 7.61/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f21])).
% 7.61/1.48  
% 7.61/1.48  fof(f144,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f108,f109])).
% 7.61/1.48  
% 7.61/1.48  fof(f145,plain,(
% 7.61/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f107,f144])).
% 7.61/1.48  
% 7.61/1.48  fof(f146,plain,(
% 7.61/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f106,f145])).
% 7.61/1.48  
% 7.61/1.48  fof(f147,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f105,f146])).
% 7.61/1.48  
% 7.61/1.48  fof(f148,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f104,f147])).
% 7.61/1.48  
% 7.61/1.48  fof(f149,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.61/1.48    inference(definition_unfolding,[],[f133,f148])).
% 7.61/1.48  
% 7.61/1.48  fof(f151,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f92,f149])).
% 7.61/1.48  
% 7.61/1.48  fof(f158,plain,(
% 7.61/1.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0) )),
% 7.61/1.48    inference(definition_unfolding,[],[f95,f151])).
% 7.61/1.48  
% 7.61/1.48  fof(f38,axiom,(
% 7.61/1.48    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f56,plain,(
% 7.61/1.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(ennf_transformation,[],[f38])).
% 7.61/1.48  
% 7.61/1.48  fof(f77,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(nnf_transformation,[],[f56])).
% 7.61/1.48  
% 7.61/1.48  fof(f78,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(flattening,[],[f77])).
% 7.61/1.48  
% 7.61/1.48  fof(f79,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(rectify,[],[f78])).
% 7.61/1.48  
% 7.61/1.48  fof(f80,plain,(
% 7.61/1.48    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK7(X0,X1) != sK8(X0,X1) | ~r2_hidden(sK7(X0,X1),X0) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & ((sK7(X0,X1) = sK8(X0,X1) & r2_hidden(sK7(X0,X1),X0)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1))))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f81,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK7(X0,X1) != sK8(X0,X1) | ~r2_hidden(sK7(X0,X1),X0) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & ((sK7(X0,X1) = sK8(X0,X1) & r2_hidden(sK7(X0,X1),X0)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f79,f80])).
% 7.61/1.48  
% 7.61/1.48  fof(f138,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK7(X0,X1),X0) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) | ~v1_relat_1(X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f81])).
% 7.61/1.48  
% 7.61/1.48  fof(f31,axiom,(
% 7.61/1.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f76,plain,(
% 7.61/1.48    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.61/1.48    inference(nnf_transformation,[],[f31])).
% 7.61/1.48  
% 7.61/1.48  fof(f127,plain,(
% 7.61/1.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 7.61/1.48    inference(cnf_transformation,[],[f76])).
% 7.61/1.48  
% 7.61/1.48  fof(f15,axiom,(
% 7.61/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f103,plain,(
% 7.61/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f15])).
% 7.61/1.48  
% 7.61/1.48  fof(f152,plain,(
% 7.61/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f103,f148])).
% 7.61/1.48  
% 7.61/1.48  fof(f175,plain,(
% 7.61/1.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0) )),
% 7.61/1.48    inference(definition_unfolding,[],[f127,f151,f152])).
% 7.61/1.48  
% 7.61/1.48  fof(f28,axiom,(
% 7.61/1.48    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f75,plain,(
% 7.61/1.48    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 7.61/1.48    inference(nnf_transformation,[],[f28])).
% 7.61/1.48  
% 7.61/1.48  fof(f123,plain,(
% 7.61/1.48    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f75])).
% 7.61/1.48  
% 7.61/1.48  fof(f171,plain,(
% 7.61/1.48    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.61/1.48    inference(definition_unfolding,[],[f123,f151,f152,f152,f152])).
% 7.61/1.48  
% 7.61/1.48  fof(f186,plain,(
% 7.61/1.48    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 7.61/1.48    inference(equality_resolution,[],[f171])).
% 7.61/1.48  
% 7.61/1.48  fof(f29,axiom,(
% 7.61/1.48    ! [X0,X1] : (X0 != X1 => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f54,plain,(
% 7.61/1.48    ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1)),
% 7.61/1.48    inference(ennf_transformation,[],[f29])).
% 7.61/1.48  
% 7.61/1.48  fof(f125,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 7.61/1.48    inference(cnf_transformation,[],[f54])).
% 7.61/1.48  
% 7.61/1.48  fof(f172,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 7.61/1.48    inference(definition_unfolding,[],[f125,f151,f148,f152,f152])).
% 7.61/1.48  
% 7.61/1.48  fof(f39,axiom,(
% 7.61/1.48    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f45,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 7.61/1.48    inference(unused_predicate_definition_removal,[],[f39])).
% 7.61/1.48  
% 7.61/1.48  fof(f57,plain,(
% 7.61/1.48    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 7.61/1.48    inference(ennf_transformation,[],[f45])).
% 7.61/1.48  
% 7.61/1.48  fof(f82,plain,(
% 7.61/1.48    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK9(X0) & r2_hidden(sK9(X0),X0)))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f83,plain,(
% 7.61/1.48    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK9(X0) & r2_hidden(sK9(X0),X0)))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f57,f82])).
% 7.61/1.48  
% 7.61/1.48  fof(f141,plain,(
% 7.61/1.48    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK9(X0),X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f83])).
% 7.61/1.48  
% 7.61/1.48  fof(f40,conjecture,(
% 7.61/1.48    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f41,negated_conjecture,(
% 7.61/1.48    ~k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.61/1.48    inference(negated_conjecture,[],[f40])).
% 7.61/1.48  
% 7.61/1.48  fof(f44,plain,(
% 7.61/1.48    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 7.61/1.48    inference(flattening,[],[f41])).
% 7.61/1.48  
% 7.61/1.48  fof(f143,plain,(
% 7.61/1.48    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 7.61/1.48    inference(cnf_transformation,[],[f44])).
% 7.61/1.48  
% 7.61/1.48  cnf(c_10,plain,
% 7.61/1.48      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 7.61/1.48      inference(cnf_transformation,[],[f158]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_28034,plain,
% 7.61/1.48      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0))))) = k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_28024,plain,
% 7.61/1.48      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0),sK7(k1_xboole_0,X0))))) = k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_28025,plain,
% 7.61/1.48      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0))))) = k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_28024]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_43,plain,
% 7.61/1.48      ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
% 7.61/1.48      | r2_hidden(sK7(X0,X1),X0)
% 7.61/1.48      | ~ v1_relat_1(X1)
% 7.61/1.48      | k6_relat_1(X0) = X1 ),
% 7.61/1.48      inference(cnf_transformation,[],[f138]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27696,plain,
% 7.61/1.48      ( k6_relat_1(X0) = X1
% 7.61/1.48      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) = iProver_top
% 7.61/1.48      | r2_hidden(sK7(X0,X1),X0) = iProver_top
% 7.61/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_35,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,X1)
% 7.61/1.48      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X1 ),
% 7.61/1.48      inference(cnf_transformation,[],[f175]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27699,plain,
% 7.61/1.48      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0
% 7.61/1.48      | r2_hidden(X1,X0) != iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27907,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_10,c_27699]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27974,plain,
% 7.61/1.48      ( k6_relat_1(X0) = k1_xboole_0
% 7.61/1.48      | r2_hidden(sK7(X0,k1_xboole_0),X0) = iProver_top
% 7.61/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_27696,c_27907]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27990,plain,
% 7.61/1.48      ( r2_hidden(sK7(X0,k1_xboole_0),X0)
% 7.61/1.48      | ~ v1_relat_1(k1_xboole_0)
% 7.61/1.48      | k6_relat_1(X0) = k1_xboole_0 ),
% 7.61/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_27974]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27992,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 7.61/1.48      | ~ v1_relat_1(k1_xboole_0)
% 7.61/1.48      | k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_27990]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27945,plain,
% 7.61/1.48      ( ~ r2_hidden(sK7(X0,X1),X0)
% 7.61/1.48      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1),sK7(X0,X1))))) != X0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_35]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27952,plain,
% 7.61/1.48      ( ~ r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 7.61/1.48      | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0))))) != k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_27945]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27821,plain,
% 7.61/1.48      ( ~ r2_hidden(sK9(X0),X0)
% 7.61/1.48      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0),sK9(X0))))) != X0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_35]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27823,plain,
% 7.61/1.48      ( ~ r2_hidden(sK9(k1_xboole_0),k1_xboole_0)
% 7.61/1.48      | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0),sK9(k1_xboole_0))))) != k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_27821]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_628,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_3976,plain,
% 7.61/1.48      ( k6_relat_1(k1_xboole_0) != X0
% 7.61/1.48      | k1_xboole_0 != X0
% 7.61/1.48      | k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_628]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_3977,plain,
% 7.61/1.48      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 7.61/1.48      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 7.61/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_3976]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_31,plain,
% 7.61/1.48      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.61/1.48      inference(cnf_transformation,[],[f186]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_87,plain,
% 7.61/1.48      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_31]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_32,plain,
% 7.61/1.48      ( X0 = X1
% 7.61/1.48      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 7.61/1.48      inference(cnf_transformation,[],[f172]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_86,plain,
% 7.61/1.48      ( k5_xboole_0(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_setfam_1(k6_enumset1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 7.61/1.48      | k1_xboole_0 = k1_xboole_0 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_32]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_48,plain,
% 7.61/1.48      ( r2_hidden(sK9(X0),X0) | v1_relat_1(X0) ),
% 7.61/1.48      inference(cnf_transformation,[],[f141]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_51,plain,
% 7.61/1.48      ( r2_hidden(sK9(k1_xboole_0),k1_xboole_0)
% 7.61/1.48      | v1_relat_1(k1_xboole_0) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_48]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_49,negated_conjecture,
% 7.61/1.48      ( k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
% 7.61/1.48      inference(cnf_transformation,[],[f143]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(contradiction,plain,
% 7.61/1.48      ( $false ),
% 7.61/1.48      inference(minisat,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_28034,c_28025,c_27992,c_27952,c_27823,c_3977,c_87,
% 7.61/1.48                 c_86,c_51,c_49]) ).
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  ------                               Statistics
% 7.61/1.48  
% 7.61/1.48  ------ Selected
% 7.61/1.48  
% 7.61/1.48  total_time:                             0.894
% 7.61/1.48  
%------------------------------------------------------------------------------

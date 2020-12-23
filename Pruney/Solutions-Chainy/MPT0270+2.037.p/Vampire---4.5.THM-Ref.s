%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 581 expanded)
%              Number of leaves         :   18 ( 177 expanded)
%              Depth                    :   15
%              Number of atoms          :  308 (1479 expanded)
%              Number of equality atoms :   61 ( 363 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f943,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f783,f135,f900,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK5(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f900,plain,(
    ! [X1] : ~ sP0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1,sK4) ),
    inference(resolution,[],[f898,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f19,f18])).

fof(f18,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f898,plain,(
    ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(subsumption_resolution,[],[f897,f860])).

fof(f860,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
      | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ) ),
    inference(subsumption_resolution,[],[f454,f704])).

fof(f704,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,k3_enumset1(X5,X5,X5,X5,X5)))
      | r2_hidden(X5,X4) ) ),
    inference(subsumption_resolution,[],[f356,f345])).

fof(f345,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) ) ),
    inference(resolution,[],[f140,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)),X2,X0)
      | r2_hidden(X2,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f64,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f48,f45,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) )
      & ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP2(X2,X0,X1) ) ),
    inference(definition_folding,[],[f17,f21])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f356,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | r2_hidden(X5,X4)
      | ~ r2_hidden(X3,k3_xboole_0(X4,k3_enumset1(X5,X5,X5,X5,X5))) ) ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | r2_hidden(X5,X4)
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k3_xboole_0(X4,k3_enumset1(X5,X5,X5,X5,X5))) ) ),
    inference(resolution,[],[f141,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f141,plain,(
    ! [X4,X5,X3] :
      ( sP2(k3_xboole_0(X3,k3_enumset1(X4,X4,X4,X4,X4)),X5,X3)
      | ~ r2_hidden(X5,X3)
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f63,f72])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f454,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(X0,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ) ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(sK3,sK4)
      | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ) ),
    inference(resolution,[],[f175,f62])).

fof(f175,plain,(
    ! [X0] :
      ( ~ sP2(k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(sK3,sK4) ) ),
    inference(superposition,[],[f64,f167])).

fof(f167,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ r2_hidden(sK3,sK4) ),
    inference(forward_demodulation,[],[f70,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(definition_unfolding,[],[f38,f68,f45,f68])).

fof(f38,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( r2_hidden(sK3,sK4)
      | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) )
    & ( ~ r2_hidden(sK3,sK4)
      | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK3,sK4)
        | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) )
      & ( ~ r2_hidden(sK3,sK4)
        | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f897,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ) ),
    inference(subsumption_resolution,[],[f474,f704])).

fof(f474,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ) ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ) ),
    inference(resolution,[],[f176,f60])).

fof(f176,plain,(
    ! [X1] :
      ( sP2(k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(sK3,sK4) ) ),
    inference(superposition,[],[f63,f167])).

fof(f135,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f134,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f105,f60])).

fof(f105,plain,(
    ! [X4,X5] :
      ( sP2(k1_xboole_0,X5,X4)
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f63,f91])).

fof(f91,plain,(
    ! [X9] : k5_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f90,plain,(
    ! [X9] :
      ( k5_xboole_0(X9,k1_xboole_0) = X9
      | ~ r1_tarski(k1_xboole_0,X9) ) ),
    inference(superposition,[],[f79,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f71,f43])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f134,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f109,f62])).

fof(f109,plain,(
    ! [X4,X5] :
      ( ~ sP2(k1_xboole_0,X5,X4)
      | r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f64,f91])).

fof(f783,plain,(
    ~ sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f782,f676])).

fof(f676,plain,(
    ! [X10,X11] :
      ( ~ sP1(X10,k3_enumset1(X11,X11,X11,X11,X11),k1_xboole_0)
      | ~ r2_hidden(X11,X10) ) ),
    inference(forward_demodulation,[],[f370,f581])).

fof(f581,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f544,f75])).

fof(f75,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f74,f43])).

fof(f544,plain,(
    ! [X2,X3] :
      ( ~ sP1(X3,k1_xboole_0,X2)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f522,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X3)
      | X2 = X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f58,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f522,plain,(
    ! [X5] : sP1(X5,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f320,f135])).

fof(f320,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X1)
      | sP1(X0,X1,X1) ) ),
    inference(factoring,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f52,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f370,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X11,X10)
      | ~ sP1(X10,k3_enumset1(X11,X11,X11,X11,X11),k3_xboole_0(k1_xboole_0,X10)) ) ),
    inference(trivial_inequality_removal,[],[f363])).

fof(f363,plain,(
    ! [X10,X11] :
      ( X10 != X10
      | ~ r2_hidden(X11,X10)
      | ~ sP1(X10,k3_enumset1(X11,X11,X11,X11,X11),k3_xboole_0(k1_xboole_0,X10)) ) ),
    inference(superposition,[],[f142,f79])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,X2) != X0
      | ~ r2_hidden(X1,X0)
      | ~ sP1(X0,k3_enumset1(X1,X1,X1,X1,X1),X2) ) ),
    inference(superposition,[],[f73,f58])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f47,f45,f68])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f782,plain,
    ( ~ sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0)
    | r2_hidden(sK3,sK4) ),
    inference(forward_demodulation,[],[f417,f581])).

fof(f417,plain,
    ( r2_hidden(sK3,sK4)
    | ~ sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,sK4)
    | ~ sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[],[f169,f79])).

fof(f169,plain,(
    ! [X0] :
      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)
      | r2_hidden(sK3,sK4)
      | ~ sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) ) ),
    inference(superposition,[],[f166,f58])).

fof(f166,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | r2_hidden(sK3,sK4) ),
    inference(forward_demodulation,[],[f69,f43])).

fof(f69,plain,
    ( r2_hidden(sK3,sK4)
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(definition_unfolding,[],[f39,f68,f45,f68])).

fof(f39,plain,
    ( r2_hidden(sK3,sK4)
    | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (14260)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (14252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (14252)Refutation not found, incomplete strategy% (14252)------------------------------
% 0.20/0.51  % (14252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14238)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (14252)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14252)Memory used [KB]: 6140
% 0.20/0.51  % (14252)Time elapsed: 0.004 s
% 0.20/0.51  % (14252)------------------------------
% 0.20/0.51  % (14252)------------------------------
% 0.20/0.51  % (14244)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (14241)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (14261)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (14253)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (14247)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (14251)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (14263)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (14246)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (14239)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (14262)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (14240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (14264)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (14243)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (14237)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (14254)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (14242)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (14254)Refutation not found, incomplete strategy% (14254)------------------------------
% 0.20/0.54  % (14254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14254)Memory used [KB]: 10618
% 0.20/0.54  % (14254)Time elapsed: 0.131 s
% 0.20/0.54  % (14254)------------------------------
% 0.20/0.54  % (14254)------------------------------
% 0.20/0.54  % (14266)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (14257)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (14256)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (14258)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (14259)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (14258)Refutation not found, incomplete strategy% (14258)------------------------------
% 0.20/0.55  % (14258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14258)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14258)Memory used [KB]: 1663
% 0.20/0.55  % (14258)Time elapsed: 0.142 s
% 0.20/0.55  % (14258)------------------------------
% 0.20/0.55  % (14258)------------------------------
% 0.20/0.55  % (14250)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (14249)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (14248)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (14255)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (14265)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (14245)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.57  % (14259)Refutation not found, incomplete strategy% (14259)------------------------------
% 0.20/0.57  % (14259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (14259)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (14259)Memory used [KB]: 10618
% 0.20/0.57  % (14259)Time elapsed: 0.146 s
% 0.20/0.57  % (14259)------------------------------
% 0.20/0.57  % (14259)------------------------------
% 0.20/0.60  % (14266)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % SZS output start Proof for theBenchmark
% 0.20/0.60  fof(f943,plain,(
% 0.20/0.60    $false),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f783,f135,f900,f52])).
% 0.20/0.60  fof(f52,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (sP0(X1,sK5(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f30])).
% 0.20/0.60  fof(f30,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 0.20/0.60  fof(f29,plain,(
% 0.20/0.60    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.60    inference(rectify,[],[f27])).
% 0.20/0.60  fof(f27,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.60    inference(nnf_transformation,[],[f19])).
% 0.20/0.60  fof(f19,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.20/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.60  fof(f900,plain,(
% 0.20/0.60    ( ! [X1] : (~sP0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1,sK4)) )),
% 0.20/0.60    inference(resolution,[],[f898,f127])).
% 0.20/0.60  fof(f127,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.60    inference(resolution,[],[f51,f74])).
% 0.20/0.60  fof(f74,plain,(
% 0.20/0.60    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 0.20/0.60    inference(equality_resolution,[],[f57])).
% 0.20/0.60  fof(f57,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.60    inference(cnf_transformation,[],[f34])).
% 0.20/0.60  fof(f34,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.60    inference(nnf_transformation,[],[f20])).
% 0.20/0.60  fof(f20,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.20/0.60    inference(definition_folding,[],[f2,f19,f18])).
% 0.20/0.60  fof(f18,plain,(
% 0.20/0.60    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.20/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.60  fof(f2,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f30])).
% 0.20/0.60  fof(f898,plain,(
% 0.20/0.60    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f897,f860])).
% 0.20/0.60  fof(f860,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f454,f704])).
% 0.20/0.60  fof(f704,plain,(
% 0.20/0.60    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,k3_enumset1(X5,X5,X5,X5,X5))) | r2_hidden(X5,X4)) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f356,f345])).
% 0.20/0.60  fof(f345,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f337])).
% 0.20/0.60  fof(f337,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1) | ~r2_hidden(X0,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) )),
% 0.20/0.60    inference(resolution,[],[f140,f62])).
% 0.20/0.60  fof(f62,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f36])).
% 0.20/0.60  fof(f36,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.60    inference(rectify,[],[f35])).
% 0.20/0.60  fof(f35,plain,(
% 0.20/0.60    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP2(X2,X0,X1)))),
% 0.20/0.60    inference(nnf_transformation,[],[f21])).
% 0.20/0.60  fof(f21,plain,(
% 0.20/0.60    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.60  fof(f140,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~sP2(k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)),X2,X0) | r2_hidden(X2,X0) | r2_hidden(X1,X0)) )),
% 0.20/0.60    inference(superposition,[],[f64,f72])).
% 0.20/0.60  fof(f72,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f48,f45,f68])).
% 0.20/0.60  fof(f68,plain,(
% 0.20/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f42,f67])).
% 0.20/0.60  fof(f67,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f44,f66])).
% 0.20/0.60  fof(f66,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f49,f65])).
% 0.20/0.60  fof(f65,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f11])).
% 0.20/0.60  fof(f11,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.60  fof(f49,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f10])).
% 0.20/0.60  fof(f10,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.60  fof(f44,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f9])).
% 0.20/0.60  fof(f9,axiom,(
% 0.20/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.60  fof(f42,plain,(
% 0.20/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f8])).
% 0.20/0.60  fof(f8,axiom,(
% 0.20/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.60  fof(f45,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f4])).
% 0.20/0.60  fof(f4,axiom,(
% 0.20/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.60  fof(f48,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f26])).
% 0.20/0.60  fof(f26,plain,(
% 0.20/0.60    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.60    inference(nnf_transformation,[],[f12])).
% 0.20/0.60  fof(f12,axiom,(
% 0.20/0.60    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.60  fof(f64,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f37])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.60    inference(nnf_transformation,[],[f22])).
% 0.20/0.60  fof(f22,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP2(X2,X0,X1))),
% 0.20/0.60    inference(definition_folding,[],[f17,f21])).
% 0.20/0.60  fof(f17,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.60    inference(ennf_transformation,[],[f3])).
% 0.20/0.60  fof(f3,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.60  fof(f356,plain,(
% 0.20/0.60    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | r2_hidden(X5,X4) | ~r2_hidden(X3,k3_xboole_0(X4,k3_enumset1(X5,X5,X5,X5,X5)))) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f348])).
% 0.20/0.60  fof(f348,plain,(
% 0.20/0.60    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | r2_hidden(X5,X4) | ~r2_hidden(X3,X4) | ~r2_hidden(X3,k3_xboole_0(X4,k3_enumset1(X5,X5,X5,X5,X5)))) )),
% 0.20/0.60    inference(resolution,[],[f141,f60])).
% 0.20/0.60  fof(f60,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f36])).
% 0.20/0.60  fof(f141,plain,(
% 0.20/0.60    ( ! [X4,X5,X3] : (sP2(k3_xboole_0(X3,k3_enumset1(X4,X4,X4,X4,X4)),X5,X3) | ~r2_hidden(X5,X3) | r2_hidden(X4,X3)) )),
% 0.20/0.60    inference(superposition,[],[f63,f72])).
% 0.20/0.60  fof(f63,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP2(X2,X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f37])).
% 0.20/0.60  fof(f454,plain,(
% 0.20/0.60    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,sK4) | ~r2_hidden(X0,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f448])).
% 0.20/0.60  fof(f448,plain,(
% 0.20/0.60    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,sK4) | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) )),
% 0.20/0.60    inference(resolution,[],[f175,f62])).
% 0.20/0.60  fof(f175,plain,(
% 0.20/0.60    ( ! [X0] : (~sP2(k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,sK4)) )),
% 0.20/0.60    inference(superposition,[],[f64,f167])).
% 0.20/0.60  fof(f167,plain,(
% 0.20/0.60    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) | ~r2_hidden(sK3,sK4)),
% 0.20/0.60    inference(forward_demodulation,[],[f70,f43])).
% 0.20/0.60  fof(f43,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f1])).
% 0.20/0.60  fof(f1,axiom,(
% 0.20/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.60  fof(f70,plain,(
% 0.20/0.60    ~r2_hidden(sK3,sK4) | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4))),
% 0.20/0.60    inference(definition_unfolding,[],[f38,f68,f45,f68])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    ~r2_hidden(sK3,sK4) | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4)),
% 0.20/0.60    inference(cnf_transformation,[],[f25])).
% 0.20/0.60  fof(f25,plain,(
% 0.20/0.60    (r2_hidden(sK3,sK4) | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)) & (~r2_hidden(sK3,sK4) | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).
% 0.20/0.60  fof(f24,plain,(
% 0.20/0.60    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK3,sK4) | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)) & (~r2_hidden(sK3,sK4) | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4)))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f23,plain,(
% 0.20/0.60    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 0.20/0.60    inference(nnf_transformation,[],[f15])).
% 0.20/0.60  fof(f15,plain,(
% 0.20/0.60    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 0.20/0.60    inference(ennf_transformation,[],[f14])).
% 0.20/0.60  fof(f14,negated_conjecture,(
% 0.20/0.60    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.60    inference(negated_conjecture,[],[f13])).
% 0.20/0.60  fof(f13,conjecture,(
% 0.20/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.20/0.60  fof(f897,plain,(
% 0.20/0.60    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f474,f704])).
% 0.20/0.60  fof(f474,plain,(
% 0.20/0.60    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,sK4) | ~r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f468])).
% 0.20/0.60  fof(f468,plain,(
% 0.20/0.60    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,sK4) | ~r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X1,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) )),
% 0.20/0.60    inference(resolution,[],[f176,f60])).
% 0.20/0.60  fof(f176,plain,(
% 0.20/0.60    ( ! [X1] : (sP2(k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,sK4)) )),
% 0.20/0.60    inference(superposition,[],[f63,f167])).
% 0.20/0.60  fof(f135,plain,(
% 0.20/0.60    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f134,f118])).
% 0.20/0.60  fof(f118,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f116])).
% 0.20/0.60  fof(f116,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.60    inference(resolution,[],[f105,f60])).
% 0.20/0.60  fof(f105,plain,(
% 0.20/0.60    ( ! [X4,X5] : (sP2(k1_xboole_0,X5,X4) | ~r2_hidden(X5,X4)) )),
% 0.20/0.60    inference(superposition,[],[f63,f91])).
% 0.20/0.60  fof(f91,plain,(
% 0.20/0.60    ( ! [X9] : (k5_xboole_0(X9,k1_xboole_0) = X9) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f90,f40])).
% 0.20/0.60  fof(f40,plain,(
% 0.20/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f6])).
% 0.20/0.60  fof(f6,axiom,(
% 0.20/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.60  fof(f90,plain,(
% 0.20/0.60    ( ! [X9] : (k5_xboole_0(X9,k1_xboole_0) = X9 | ~r1_tarski(k1_xboole_0,X9)) )),
% 0.20/0.60    inference(superposition,[],[f79,f46])).
% 0.20/0.60  fof(f46,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f16])).
% 0.20/0.60  fof(f16,plain,(
% 0.20/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.60    inference(ennf_transformation,[],[f5])).
% 0.20/0.60  fof(f5,axiom,(
% 0.20/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.60  fof(f79,plain,(
% 0.20/0.60    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.20/0.60    inference(superposition,[],[f71,f43])).
% 0.20/0.60  fof(f71,plain,(
% 0.20/0.60    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.60    inference(definition_unfolding,[],[f41,f45])).
% 0.20/0.60  fof(f41,plain,(
% 0.20/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.60    inference(cnf_transformation,[],[f7])).
% 0.20/0.60  fof(f7,axiom,(
% 0.20/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.60  fof(f134,plain,(
% 0.20/0.60    ( ! [X2,X3] : (r2_hidden(X2,X3) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.60  fof(f132,plain,(
% 0.20/0.60    ( ! [X2,X3] : (r2_hidden(X2,X3) | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.60    inference(resolution,[],[f109,f62])).
% 0.20/0.60  fof(f109,plain,(
% 0.20/0.60    ( ! [X4,X5] : (~sP2(k1_xboole_0,X5,X4) | r2_hidden(X5,X4)) )),
% 0.20/0.60    inference(superposition,[],[f64,f91])).
% 0.20/0.60  fof(f783,plain,(
% 0.20/0.60    ~sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0)),
% 0.20/0.60    inference(subsumption_resolution,[],[f782,f676])).
% 0.20/0.60  fof(f676,plain,(
% 0.20/0.60    ( ! [X10,X11] : (~sP1(X10,k3_enumset1(X11,X11,X11,X11,X11),k1_xboole_0) | ~r2_hidden(X11,X10)) )),
% 0.20/0.60    inference(forward_demodulation,[],[f370,f581])).
% 0.20/0.60  fof(f581,plain,(
% 0.20/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.60    inference(resolution,[],[f544,f75])).
% 0.20/0.60  fof(f75,plain,(
% 0.20/0.60    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X1,X0))) )),
% 0.20/0.60    inference(superposition,[],[f74,f43])).
% 0.20/0.60  fof(f544,plain,(
% 0.20/0.60    ( ! [X2,X3] : (~sP1(X3,k1_xboole_0,X2) | k1_xboole_0 = X2) )),
% 0.20/0.60    inference(resolution,[],[f522,f92])).
% 0.20/0.60  fof(f92,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X3) | X2 = X3 | ~sP1(X0,X1,X2)) )),
% 0.20/0.60    inference(superposition,[],[f58,f58])).
% 0.20/0.60  fof(f58,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f34])).
% 0.20/0.60  fof(f522,plain,(
% 0.20/0.60    ( ! [X5] : (sP1(X5,k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.60    inference(resolution,[],[f320,f135])).
% 0.20/0.60  fof(f320,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X1) | sP1(X0,X1,X1)) )),
% 0.20/0.60    inference(factoring,[],[f147])).
% 0.20/0.60  fof(f147,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X1)) )),
% 0.20/0.60    inference(resolution,[],[f52,f55])).
% 0.20/0.60  fof(f55,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f33])).
% 0.20/0.60  fof(f33,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.60    inference(rectify,[],[f32])).
% 0.20/0.60  fof(f32,plain,(
% 0.20/0.60    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.20/0.60    inference(flattening,[],[f31])).
% 0.20/0.60  fof(f31,plain,(
% 0.20/0.60    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.20/0.60    inference(nnf_transformation,[],[f18])).
% 0.20/0.60  fof(f370,plain,(
% 0.20/0.60    ( ! [X10,X11] : (~r2_hidden(X11,X10) | ~sP1(X10,k3_enumset1(X11,X11,X11,X11,X11),k3_xboole_0(k1_xboole_0,X10))) )),
% 0.20/0.60    inference(trivial_inequality_removal,[],[f363])).
% 0.20/0.60  fof(f363,plain,(
% 0.20/0.60    ( ! [X10,X11] : (X10 != X10 | ~r2_hidden(X11,X10) | ~sP1(X10,k3_enumset1(X11,X11,X11,X11,X11),k3_xboole_0(k1_xboole_0,X10))) )),
% 0.20/0.60    inference(superposition,[],[f142,f79])).
% 0.20/0.60  fof(f142,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X2) != X0 | ~r2_hidden(X1,X0) | ~sP1(X0,k3_enumset1(X1,X1,X1,X1,X1),X2)) )),
% 0.20/0.60    inference(superposition,[],[f73,f58])).
% 0.20/0.60  fof(f73,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f47,f45,f68])).
% 1.95/0.62  fof(f47,plain,(
% 1.95/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.95/0.62    inference(cnf_transformation,[],[f26])).
% 1.95/0.62  fof(f782,plain,(
% 1.95/0.62    ~sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) | r2_hidden(sK3,sK4)),
% 1.95/0.62    inference(forward_demodulation,[],[f417,f581])).
% 1.95/0.62  fof(f417,plain,(
% 1.95/0.62    r2_hidden(sK3,sK4) | ~sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),
% 1.95/0.62    inference(trivial_inequality_removal,[],[f412])).
% 1.95/0.62  fof(f412,plain,(
% 1.95/0.62    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) | r2_hidden(sK3,sK4) | ~sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),
% 1.95/0.62    inference(superposition,[],[f169,f79])).
% 1.95/0.62  fof(f169,plain,(
% 1.95/0.62    ( ! [X0] : (k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) | r2_hidden(sK3,sK4) | ~sP1(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0)) )),
% 1.95/0.62    inference(superposition,[],[f166,f58])).
% 1.95/0.62  fof(f166,plain,(
% 1.95/0.62    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) | r2_hidden(sK3,sK4)),
% 1.95/0.62    inference(forward_demodulation,[],[f69,f43])).
% 1.95/0.62  fof(f69,plain,(
% 1.95/0.62    r2_hidden(sK3,sK4) | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4))),
% 1.95/0.62    inference(definition_unfolding,[],[f39,f68,f45,f68])).
% 1.95/0.62  fof(f39,plain,(
% 1.95/0.62    r2_hidden(sK3,sK4) | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)),
% 1.95/0.62    inference(cnf_transformation,[],[f25])).
% 1.95/0.62  % SZS output end Proof for theBenchmark
% 1.95/0.62  % (14266)------------------------------
% 1.95/0.62  % (14266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.62  % (14266)Termination reason: Refutation
% 1.95/0.62  
% 1.95/0.62  % (14266)Memory used [KB]: 2174
% 1.95/0.62  % (14266)Time elapsed: 0.174 s
% 1.95/0.62  % (14266)------------------------------
% 1.95/0.62  % (14266)------------------------------
% 1.95/0.62  % (14236)Success in time 0.256 s
%------------------------------------------------------------------------------

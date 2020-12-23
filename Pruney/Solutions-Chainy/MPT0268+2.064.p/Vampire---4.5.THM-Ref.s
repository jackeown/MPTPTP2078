%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 122 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  237 ( 386 expanded)
%              Number of equality atoms :   86 ( 123 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f67,f130,f145])).

fof(f145,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f139,f65])).

fof(f65,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f139,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f133,f74])).

fof(f74,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(X6,k2_enumset1(X7,X7,X7,X8))
      | ~ r2_hidden(X7,X6) ) ),
    inference(resolution,[],[f35,f70])).

fof(f70,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f57,f56])).

fof(f56,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK4(X0,X1,X2) != X0
              & sK4(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X0
            | sK4(X0,X1,X2) = X1
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X0
            & sK4(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X0
          | sK4(X0,X1,X2) = X1
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f57,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f133,plain,
    ( r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( sK1 != sK1
    | r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl5_1 ),
    inference(superposition,[],[f51,f60])).

fof(f60,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f130,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f122,f61])).

fof(f61,plain,
    ( sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f122,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | spl5_2 ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f92,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,X7)
      | k5_xboole_0(X7,k3_xboole_0(X7,k2_enumset1(X6,X6,X6,X6))) = X7 ) ),
    inference(resolution,[],[f87,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f84,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X1,X2),X0)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f49,f63,f59])).

fof(f49,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f28,f31,f47])).

fof(f28,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( r2_hidden(sK2,sK1)
      | sK1 != k4_xboole_0(sK1,k1_tarski(sK2)) )
    & ( ~ r2_hidden(sK2,sK1)
      | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK2,sK1)
        | sK1 != k4_xboole_0(sK1,k1_tarski(sK2)) )
      & ( ~ r2_hidden(sK2,sK1)
        | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f66,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f48,f63,f59])).

fof(f48,plain,
    ( r2_hidden(sK2,sK1)
    | sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f29,f31,f47])).

fof(f29,plain,
    ( r2_hidden(sK2,sK1)
    | sK1 != k4_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15334)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15334)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (15350)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (15341)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f66,f67,f130,f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    $false | (~spl5_1 | ~spl5_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    r2_hidden(sK2,sK1) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~r2_hidden(sK2,sK1) | ~spl5_1),
% 0.21/0.51    inference(resolution,[],[f133,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X6,X8,X7] : (~r1_xboole_0(X6,k2_enumset1(X7,X7,X7,X8)) | ~r2_hidden(X7,X6)) )),
% 0.21/0.51    inference(resolution,[],[f35,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.51    inference(resolution,[],[f57,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.21/0.51    inference(definition_unfolding,[],[f45,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.51    inference(definition_folding,[],[f4,f14])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl5_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    sK1 != sK1 | r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl5_1),
% 0.21/0.51    inference(superposition,[],[f51,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl5_1 <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f38,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl5_1 | spl5_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    $false | (spl5_1 | spl5_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | spl5_2),
% 0.21/0.51    inference(resolution,[],[f92,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~r2_hidden(sK2,sK1) | spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f63])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X6,X7] : (r2_hidden(X6,X7) | k5_xboole_0(X7,k3_xboole_0(X7,k2_enumset1(X6,X6,X6,X6))) = X7) )),
% 0.21/0.51    inference(resolution,[],[f87,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f37,f31])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) | r2_hidden(X1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f84,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f36,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f30,f32])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.21/0.51    inference(resolution,[],[f72,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X1,X2),X0) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X2)) )),
% 0.21/0.51    inference(resolution,[],[f35,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f63,f59])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~r2_hidden(sK2,sK1) | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.51    inference(definition_unfolding,[],[f28,f31,f47])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ~r2_hidden(sK2,sK1) | sK1 = k4_xboole_0(sK1,k1_tarski(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    (r2_hidden(sK2,sK1) | sK1 != k4_xboole_0(sK1,k1_tarski(sK2))) & (~r2_hidden(sK2,sK1) | sK1 = k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK2,sK1) | sK1 != k4_xboole_0(sK1,k1_tarski(sK2))) & (~r2_hidden(sK2,sK1) | sK1 = k4_xboole_0(sK1,k1_tarski(sK2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ~spl5_1 | spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f63,f59])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    r2_hidden(sK2,sK1) | sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f31,f47])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    r2_hidden(sK2,sK1) | sK1 != k4_xboole_0(sK1,k1_tarski(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15334)------------------------------
% 0.21/0.52  % (15334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15334)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15334)Memory used [KB]: 10746
% 0.21/0.52  % (15334)Time elapsed: 0.091 s
% 0.21/0.52  % (15334)------------------------------
% 0.21/0.52  % (15334)------------------------------
% 0.21/0.52  % (15327)Success in time 0.155 s
%------------------------------------------------------------------------------

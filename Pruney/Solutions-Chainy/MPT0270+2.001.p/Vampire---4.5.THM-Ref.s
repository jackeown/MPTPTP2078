%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:56 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 248 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  414 ( 973 expanded)
%              Number of equality atoms :  125 ( 199 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f670,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f126,f140,f163,f416,f540,f605,f669])).

fof(f669,plain,
    ( spl9_3
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | spl9_3
    | ~ spl9_10 ),
    inference(resolution,[],[f660,f134])).

fof(f134,plain,
    ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_3
  <=> r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f660,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ spl9_10 ),
    inference(resolution,[],[f539,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f539,plain,
    ( r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl9_10
  <=> r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f605,plain,(
    ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | ~ spl9_9 ),
    inference(resolution,[],[f597,f596])).

fof(f596,plain,
    ( ~ r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),sK4)
    | ~ spl9_9 ),
    inference(resolution,[],[f535,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f80,f112])).

fof(f112,plain,(
    ! [X0,X1] : sP1(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f5,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

% (17439)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f535,plain,
    ( r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(sK4,sK4))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl9_9
  <=> r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f597,plain,
    ( r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),sK4)
    | ~ spl9_9 ),
    inference(resolution,[],[f535,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f79,f112])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f540,plain,
    ( spl9_9
    | spl9_10
    | spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f520,f132,f122,f537,f533])).

fof(f122,plain,
    ( spl9_2
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f520,plain,
    ( r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(sK4,sK4))
    | spl9_2
    | spl9_3 ),
    inference(resolution,[],[f453,f141])).

fof(f141,plain,
    ( r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl9_3 ),
    inference(resolution,[],[f134,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
        | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
        | r2_hidden(X0,k4_xboole_0(sK4,sK4)) )
    | spl9_2 ),
    inference(resolution,[],[f429,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f429,plain,
    ( sP1(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK4,sK4))
    | spl9_2 ),
    inference(superposition,[],[f173,f417])).

fof(f417,plain,
    ( sK4 = k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | spl9_2 ),
    inference(resolution,[],[f123,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f69,f98])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f123,plain,
    ( ~ r2_hidden(sK3,sK4)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f173,plain,(
    ! [X14,X15] : sP1(k4_xboole_0(X14,X15),X14,k4_xboole_0(X15,k4_xboole_0(X15,X14))) ),
    inference(superposition,[],[f112,f102])).

fof(f102,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f57,f59,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f416,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f405,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(resolution,[],[f116,f115])).

fof(f115,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( ( ( sK8(X0,X1,X2,X3) != X0
              & sK8(X0,X1,X2,X3) != X1
              & sK8(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sK8(X0,X1,X2,X3) = X0
            | sK8(X0,X1,X2,X3) = X1
            | sK8(X0,X1,X2,X3) = X2
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK8(X0,X1,X2,X3) != X0
            & sK8(X0,X1,X2,X3) != X1
            & sK8(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sK8(X0,X1,X2,X3) = X0
          | sK8(X0,X1,X2,X3) = X1
          | sK8(X0,X1,X2,X3) = X2
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP2(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP2(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP2(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP2(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( sP2(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f116,plain,(
    ! [X2,X0,X1] : sP2(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f95,f70])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP2(X2,X1,X0,X3) )
      & ( sP2(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP2(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f19,f24])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f405,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f370,f124])).

fof(f124,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f370,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK4)
        | ~ r2_hidden(X3,k2_enumset1(sK3,sK3,sK3,sK3)) )
    | ~ spl9_1 ),
    inference(superposition,[],[f164,f119])).

fof(f119,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl9_1
  <=> k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f163,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl9_4 ),
    inference(resolution,[],[f158,f138])).

fof(f138,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_4
  <=> r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f158,plain,
    ( r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl9_4 ),
    inference(resolution,[],[f157,f67])).

fof(f157,plain,
    ( r2_hidden(sK5(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl9_4 ),
    inference(resolution,[],[f156,f142])).

fof(f142,plain,
    ( r2_hidden(sK5(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | spl9_4 ),
    inference(resolution,[],[f138,f66])).

fof(f140,plain,
    ( ~ spl9_4
    | ~ spl9_3
    | spl9_1 ),
    inference(avatar_split_clause,[],[f128,f118,f132,f136])).

fof(f128,plain,
    ( ~ r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl9_1 ),
    inference(extensionality_resolution,[],[f64,f120])).

fof(f120,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f126,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f101,f122,f118])).

fof(f101,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f54,f98,f98])).

fof(f54,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( r2_hidden(sK3,sK4)
      | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) )
    & ( ~ r2_hidden(sK3,sK4)
      | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f27])).

fof(f27,plain,
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

% (17454)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f26,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f125,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f100,f122,f118])).

fof(f100,plain,
    ( r2_hidden(sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f55,f98,f98])).

fof(f55,plain,
    ( r2_hidden(sK3,sK4)
    | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 09:39:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.49  % (17432)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.49  % (17448)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.49  % (17430)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.49  % (17436)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.49  % (17435)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.50  % (17457)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.50  % (17440)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.50  % (17450)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.50  % (17445)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.50  % (17442)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.50  % (17453)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.50  % (17448)Refutation not found, incomplete strategy% (17448)------------------------------
% 0.18/0.50  % (17448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (17448)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (17448)Memory used [KB]: 10746
% 0.18/0.50  % (17448)Time elapsed: 0.126 s
% 0.18/0.50  % (17448)------------------------------
% 0.18/0.50  % (17448)------------------------------
% 0.18/0.51  % (17434)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.51  % (17450)Refutation not found, incomplete strategy% (17450)------------------------------
% 0.18/0.51  % (17450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (17450)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (17450)Memory used [KB]: 10746
% 0.18/0.51  % (17450)Time elapsed: 0.067 s
% 0.18/0.51  % (17450)------------------------------
% 0.18/0.51  % (17450)------------------------------
% 0.18/0.51  % (17444)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.52  % (17433)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.52  % (17431)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.52  % (17449)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.52  % (17429)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.52  % (17445)Refutation not found, incomplete strategy% (17445)------------------------------
% 0.18/0.52  % (17445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (17445)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (17445)Memory used [KB]: 10618
% 0.18/0.52  % (17445)Time elapsed: 0.142 s
% 0.18/0.52  % (17445)------------------------------
% 0.18/0.52  % (17445)------------------------------
% 0.18/0.53  % (17446)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.53  % (17441)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.53  % (17437)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.53  % (17440)Refutation found. Thanks to Tanya!
% 0.18/0.53  % SZS status Theorem for theBenchmark
% 0.18/0.53  % SZS output start Proof for theBenchmark
% 0.18/0.53  fof(f670,plain,(
% 0.18/0.53    $false),
% 0.18/0.53    inference(avatar_sat_refutation,[],[f125,f126,f140,f163,f416,f540,f605,f669])).
% 0.18/0.53  fof(f669,plain,(
% 0.18/0.53    spl9_3 | ~spl9_10),
% 0.18/0.53    inference(avatar_contradiction_clause,[],[f665])).
% 0.18/0.53  fof(f665,plain,(
% 0.18/0.53    $false | (spl9_3 | ~spl9_10)),
% 0.18/0.53    inference(resolution,[],[f660,f134])).
% 0.18/0.53  fof(f134,plain,(
% 0.18/0.53    ~r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | spl9_3),
% 0.18/0.53    inference(avatar_component_clause,[],[f132])).
% 0.18/0.53  fof(f132,plain,(
% 0.18/0.53    spl9_3 <=> r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))),
% 0.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.18/0.53  fof(f660,plain,(
% 0.18/0.53    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | ~spl9_10),
% 0.18/0.53    inference(resolution,[],[f539,f67])).
% 0.18/0.53  fof(f67,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f34])).
% 0.18/0.53  fof(f34,plain,(
% 0.18/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 0.18/0.53  fof(f33,plain,(
% 0.18/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.18/0.53    introduced(choice_axiom,[])).
% 0.18/0.53  fof(f32,plain,(
% 0.18/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.53    inference(rectify,[],[f31])).
% 0.18/0.53  fof(f31,plain,(
% 0.18/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.53    inference(nnf_transformation,[],[f18])).
% 0.18/0.53  fof(f18,plain,(
% 0.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.53    inference(ennf_transformation,[],[f3])).
% 0.18/0.53  fof(f3,axiom,(
% 0.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.53  fof(f539,plain,(
% 0.18/0.53    r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | ~spl9_10),
% 0.18/0.53    inference(avatar_component_clause,[],[f537])).
% 0.18/0.53  fof(f537,plain,(
% 0.18/0.53    spl9_10 <=> r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))),
% 0.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.18/0.53  fof(f605,plain,(
% 0.18/0.53    ~spl9_9),
% 0.18/0.53    inference(avatar_contradiction_clause,[],[f601])).
% 0.18/0.53  fof(f601,plain,(
% 0.18/0.53    $false | ~spl9_9),
% 0.18/0.53    inference(resolution,[],[f597,f596])).
% 0.18/0.53  fof(f596,plain,(
% 0.18/0.53    ~r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),sK4) | ~spl9_9),
% 0.18/0.53    inference(resolution,[],[f535,f164])).
% 0.18/0.53  fof(f164,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 0.18/0.53    inference(resolution,[],[f80,f112])).
% 0.18/0.53  fof(f112,plain,(
% 0.18/0.53    ( ! [X0,X1] : (sP1(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.18/0.53    inference(equality_resolution,[],[f85])).
% 0.18/0.53  fof(f85,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.18/0.53    inference(cnf_transformation,[],[f47])).
% 0.18/0.53  fof(f47,plain,(
% 0.18/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.18/0.53    inference(nnf_transformation,[],[f23])).
% 0.18/0.53  fof(f23,plain,(
% 0.18/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 0.18/0.53    inference(definition_folding,[],[f5,f22])).
% 0.18/0.53  fof(f22,plain,(
% 0.18/0.53    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.18/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.18/0.53  fof(f5,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.18/0.53  fof(f80,plain,(
% 0.18/0.53    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f46])).
% 0.18/0.53  fof(f46,plain,(
% 0.18/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.18/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 0.18/0.53  % (17439)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.53  fof(f45,plain,(
% 0.18/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.18/0.53    introduced(choice_axiom,[])).
% 0.18/0.53  fof(f44,plain,(
% 0.18/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.18/0.53    inference(rectify,[],[f43])).
% 0.18/0.53  fof(f43,plain,(
% 0.18/0.53    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.18/0.53    inference(flattening,[],[f42])).
% 0.18/0.53  fof(f42,plain,(
% 0.18/0.53    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.18/0.53    inference(nnf_transformation,[],[f22])).
% 0.18/0.53  fof(f535,plain,(
% 0.18/0.53    r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(sK4,sK4)) | ~spl9_9),
% 0.18/0.53    inference(avatar_component_clause,[],[f533])).
% 0.18/0.53  fof(f533,plain,(
% 0.18/0.53    spl9_9 <=> r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(sK4,sK4))),
% 0.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.18/0.53  fof(f597,plain,(
% 0.18/0.53    r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),sK4) | ~spl9_9),
% 0.18/0.53    inference(resolution,[],[f535,f156])).
% 0.18/0.53  fof(f156,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 0.18/0.53    inference(resolution,[],[f79,f112])).
% 0.18/0.53  fof(f79,plain,(
% 0.18/0.53    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f46])).
% 0.18/0.53  fof(f540,plain,(
% 0.18/0.53    spl9_9 | spl9_10 | spl9_2 | spl9_3),
% 0.18/0.53    inference(avatar_split_clause,[],[f520,f132,f122,f537,f533])).
% 0.18/0.53  fof(f122,plain,(
% 0.18/0.53    spl9_2 <=> r2_hidden(sK3,sK4)),
% 0.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.18/0.53  fof(f520,plain,(
% 0.18/0.53    r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k4_xboole_0(sK4,sK4)) | (spl9_2 | spl9_3)),
% 0.18/0.53    inference(resolution,[],[f453,f141])).
% 0.18/0.53  fof(f141,plain,(
% 0.18/0.53    r2_hidden(sK5(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),k2_enumset1(sK3,sK3,sK3,sK3)) | spl9_3),
% 0.18/0.53    inference(resolution,[],[f134,f66])).
% 0.18/0.53  fof(f66,plain,(
% 0.18/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f34])).
% 0.18/0.53  fof(f453,plain,(
% 0.18/0.53    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | r2_hidden(X0,k4_xboole_0(sK4,sK4))) ) | spl9_2),
% 0.18/0.53    inference(resolution,[],[f429,f81])).
% 0.18/0.53  fof(f81,plain,(
% 0.18/0.53    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f46])).
% 0.18/0.53  fof(f429,plain,(
% 0.18/0.53    sP1(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK4,sK4)) | spl9_2),
% 0.18/0.53    inference(superposition,[],[f173,f417])).
% 0.18/0.53  fof(f417,plain,(
% 0.18/0.53    sK4 = k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) | spl9_2),
% 0.18/0.53    inference(resolution,[],[f123,f103])).
% 0.18/0.53  fof(f103,plain,(
% 0.18/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 0.18/0.53    inference(definition_unfolding,[],[f69,f98])).
% 0.18/0.53  fof(f98,plain,(
% 0.18/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.53    inference(definition_unfolding,[],[f56,f97])).
% 0.18/0.53  fof(f97,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.53    inference(definition_unfolding,[],[f58,f70])).
% 0.18/0.53  fof(f70,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f12])).
% 0.18/0.53  fof(f12,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.53  fof(f58,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f11])).
% 0.18/0.53  fof(f11,axiom,(
% 0.18/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.53  fof(f56,plain,(
% 0.18/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f10])).
% 0.18/0.53  fof(f10,axiom,(
% 0.18/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.53  fof(f69,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f35])).
% 0.18/0.53  fof(f35,plain,(
% 0.18/0.53    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.18/0.53    inference(nnf_transformation,[],[f13])).
% 0.18/0.53  fof(f13,axiom,(
% 0.18/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.18/0.53  fof(f123,plain,(
% 0.18/0.53    ~r2_hidden(sK3,sK4) | spl9_2),
% 0.18/0.53    inference(avatar_component_clause,[],[f122])).
% 0.18/0.53  fof(f173,plain,(
% 0.18/0.53    ( ! [X14,X15] : (sP1(k4_xboole_0(X14,X15),X14,k4_xboole_0(X15,k4_xboole_0(X15,X14)))) )),
% 0.18/0.53    inference(superposition,[],[f112,f102])).
% 0.18/0.53  fof(f102,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.18/0.53    inference(definition_unfolding,[],[f57,f59,f59])).
% 0.18/0.53  fof(f59,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f8])).
% 0.18/0.53  fof(f8,axiom,(
% 0.18/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.18/0.53  fof(f57,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f2])).
% 0.18/0.53  fof(f2,axiom,(
% 0.18/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.18/0.53  fof(f416,plain,(
% 0.18/0.53    ~spl9_1 | ~spl9_2),
% 0.18/0.53    inference(avatar_contradiction_clause,[],[f410])).
% 0.18/0.53  fof(f410,plain,(
% 0.18/0.53    $false | (~spl9_1 | ~spl9_2)),
% 0.18/0.53    inference(resolution,[],[f405,f148])).
% 0.18/0.53  fof(f148,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.18/0.53    inference(resolution,[],[f116,f115])).
% 0.18/0.53  fof(f115,plain,(
% 0.18/0.53    ( ! [X0,X5,X3,X1] : (~sP2(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.18/0.53    inference(equality_resolution,[],[f88])).
% 0.18/0.53  fof(f88,plain,(
% 0.18/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP2(X0,X1,X2,X3)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f52])).
% 0.18/0.53  fof(f52,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 0.18/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).
% 0.18/0.53  fof(f51,plain,(
% 0.18/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 0.18/0.53    introduced(choice_axiom,[])).
% 0.18/0.53  fof(f50,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 0.18/0.53    inference(rectify,[],[f49])).
% 0.18/0.53  fof(f49,plain,(
% 0.18/0.53    ! [X2,X1,X0,X3] : ((sP2(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP2(X2,X1,X0,X3)))),
% 0.18/0.53    inference(flattening,[],[f48])).
% 0.18/0.53  fof(f48,plain,(
% 0.18/0.53    ! [X2,X1,X0,X3] : ((sP2(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP2(X2,X1,X0,X3)))),
% 0.18/0.53    inference(nnf_transformation,[],[f24])).
% 0.18/0.53  fof(f24,plain,(
% 0.18/0.53    ! [X2,X1,X0,X3] : (sP2(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.18/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.18/0.53  fof(f116,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (sP2(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.18/0.53    inference(equality_resolution,[],[f108])).
% 0.18/0.53  fof(f108,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (sP2(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.18/0.53    inference(definition_unfolding,[],[f95,f70])).
% 0.18/0.53  fof(f95,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (sP2(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.18/0.53    inference(cnf_transformation,[],[f53])).
% 0.18/0.53  fof(f53,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP2(X2,X1,X0,X3)) & (sP2(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.18/0.53    inference(nnf_transformation,[],[f25])).
% 0.18/0.53  fof(f25,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP2(X2,X1,X0,X3))),
% 0.18/0.53    inference(definition_folding,[],[f19,f24])).
% 0.18/0.53  fof(f19,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.18/0.53    inference(ennf_transformation,[],[f9])).
% 0.18/0.53  fof(f9,axiom,(
% 0.18/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.18/0.53  fof(f405,plain,(
% 0.18/0.53    ~r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | (~spl9_1 | ~spl9_2)),
% 0.18/0.53    inference(resolution,[],[f370,f124])).
% 0.18/0.53  fof(f124,plain,(
% 0.18/0.53    r2_hidden(sK3,sK4) | ~spl9_2),
% 0.18/0.53    inference(avatar_component_clause,[],[f122])).
% 0.18/0.53  fof(f370,plain,(
% 0.18/0.53    ( ! [X3] : (~r2_hidden(X3,sK4) | ~r2_hidden(X3,k2_enumset1(sK3,sK3,sK3,sK3))) ) | ~spl9_1),
% 0.18/0.53    inference(superposition,[],[f164,f119])).
% 0.18/0.53  fof(f119,plain,(
% 0.18/0.53    k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) | ~spl9_1),
% 0.18/0.53    inference(avatar_component_clause,[],[f118])).
% 0.18/0.53  fof(f118,plain,(
% 0.18/0.53    spl9_1 <=> k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 0.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.18/0.53  fof(f163,plain,(
% 0.18/0.53    spl9_4),
% 0.18/0.53    inference(avatar_contradiction_clause,[],[f160])).
% 0.18/0.53  fof(f160,plain,(
% 0.18/0.53    $false | spl9_4),
% 0.18/0.53    inference(resolution,[],[f158,f138])).
% 0.18/0.53  fof(f138,plain,(
% 0.18/0.53    ~r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) | spl9_4),
% 0.18/0.53    inference(avatar_component_clause,[],[f136])).
% 0.18/0.53  fof(f136,plain,(
% 0.18/0.53    spl9_4 <=> r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.18/0.53  fof(f158,plain,(
% 0.18/0.53    r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) | spl9_4),
% 0.18/0.53    inference(resolution,[],[f157,f67])).
% 0.18/0.53  fof(f157,plain,(
% 0.18/0.53    r2_hidden(sK5(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) | spl9_4),
% 0.18/0.53    inference(resolution,[],[f156,f142])).
% 0.18/0.53  fof(f142,plain,(
% 0.18/0.53    r2_hidden(sK5(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | spl9_4),
% 0.18/0.53    inference(resolution,[],[f138,f66])).
% 0.18/0.53  fof(f140,plain,(
% 0.18/0.53    ~spl9_4 | ~spl9_3 | spl9_1),
% 0.18/0.53    inference(avatar_split_clause,[],[f128,f118,f132,f136])).
% 0.18/0.53  fof(f128,plain,(
% 0.18/0.53    ~r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | ~r1_tarski(k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) | spl9_1),
% 0.18/0.53    inference(extensionality_resolution,[],[f64,f120])).
% 0.18/0.53  fof(f120,plain,(
% 0.18/0.53    k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) | spl9_1),
% 0.18/0.53    inference(avatar_component_clause,[],[f118])).
% 0.18/0.53  fof(f64,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f30])).
% 0.18/0.53  fof(f30,plain,(
% 0.18/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.53    inference(flattening,[],[f29])).
% 0.18/0.53  fof(f29,plain,(
% 0.18/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.53    inference(nnf_transformation,[],[f6])).
% 0.18/0.53  fof(f6,axiom,(
% 0.18/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.53  fof(f126,plain,(
% 0.18/0.53    spl9_1 | ~spl9_2),
% 0.18/0.53    inference(avatar_split_clause,[],[f101,f122,f118])).
% 0.18/0.53  fof(f101,plain,(
% 0.18/0.53    ~r2_hidden(sK3,sK4) | k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 0.18/0.53    inference(definition_unfolding,[],[f54,f98,f98])).
% 0.18/0.53  fof(f54,plain,(
% 0.18/0.53    ~r2_hidden(sK3,sK4) | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4)),
% 0.18/0.53    inference(cnf_transformation,[],[f28])).
% 0.18/0.53  fof(f28,plain,(
% 0.18/0.53    (r2_hidden(sK3,sK4) | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)) & (~r2_hidden(sK3,sK4) | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4))),
% 0.18/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f27])).
% 0.18/0.53  fof(f27,plain,(
% 0.18/0.53    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK3,sK4) | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)) & (~r2_hidden(sK3,sK4) | k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK4)))),
% 0.18/0.53    introduced(choice_axiom,[])).
% 0.18/0.53  % (17454)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.18/0.53  fof(f26,plain,(
% 0.18/0.53    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 0.18/0.53    inference(nnf_transformation,[],[f16])).
% 0.18/0.53  fof(f16,plain,(
% 0.18/0.53    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 0.18/0.53    inference(ennf_transformation,[],[f15])).
% 0.18/0.53  fof(f15,negated_conjecture,(
% 0.18/0.53    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.18/0.53    inference(negated_conjecture,[],[f14])).
% 0.18/0.53  fof(f14,conjecture,(
% 0.18/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.18/0.53  fof(f125,plain,(
% 0.18/0.53    ~spl9_1 | spl9_2),
% 0.18/0.53    inference(avatar_split_clause,[],[f100,f122,f118])).
% 0.18/0.53  fof(f100,plain,(
% 0.18/0.53    r2_hidden(sK3,sK4) | k2_enumset1(sK3,sK3,sK3,sK3) != k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 0.18/0.53    inference(definition_unfolding,[],[f55,f98,f98])).
% 0.18/0.53  fof(f55,plain,(
% 0.18/0.53    r2_hidden(sK3,sK4) | k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)),
% 0.18/0.53    inference(cnf_transformation,[],[f28])).
% 0.18/0.53  % SZS output end Proof for theBenchmark
% 0.18/0.53  % (17440)------------------------------
% 0.18/0.53  % (17440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (17440)Termination reason: Refutation
% 1.50/0.53  
% 1.50/0.53  % (17440)Memory used [KB]: 6524
% 1.50/0.53  % (17440)Time elapsed: 0.152 s
% 1.50/0.53  % (17440)------------------------------
% 1.50/0.53  % (17440)------------------------------
% 1.50/0.54  % (17427)Success in time 0.202 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:40:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 264 expanded)
%              Number of leaves         :   30 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  365 ( 607 expanded)
%              Number of equality atoms :   90 ( 190 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f590,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f116,f145,f152,f387,f589])).

fof(f589,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f582,f114])).

fof(f114,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f582,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f578,f105])).

fof(f105,plain,(
    ! [X2,X3,X1] : sP2(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X1,X0] :
      ( sP2(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ sP2(X0,sK5,sK5,sK5)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f342,f554])).

fof(f554,plain,
    ( ! [X40] :
        ( ~ r2_hidden(X40,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
        | ~ r2_hidden(X40,sK4) )
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f286,f392])).

fof(f392,plain,
    ( r1_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ spl10_1 ),
    inference(superposition,[],[f98,f109])).

fof(f109,plain,
    ( sK4 = k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl10_1
  <=> sK4 = k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f98,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f286,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1) )
    | ~ spl10_4 ),
    inference(resolution,[],[f279,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f279,plain,
    ( ! [X6,X8,X7] :
        ( ~ sP0(X6,X7,X8)
        | ~ r1_xboole_0(X6,X8) )
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f276,f144])).

fof(f144,plain,
    ( ! [X6] : ~ r2_hidden(X6,k1_xboole_0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl10_4
  <=> ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f276,plain,(
    ! [X6,X8,X7] :
      ( ~ sP0(X6,X7,X8)
      | r2_hidden(X7,k1_xboole_0)
      | ~ r1_xboole_0(X6,X8) ) ),
    inference(resolution,[],[f68,f135])).

fof(f135,plain,(
    ! [X12,X11] :
      ( sP1(X12,X11,k1_xboole_0)
      | ~ r1_xboole_0(X11,X12) ) ),
    inference(superposition,[],[f117,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f117,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f102,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f102,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f26,f25])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP0(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP0(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f342,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f106,f78])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ sP2(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ sP2(sK9(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
          & ( sP2(sK9(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP2(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP2(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP2(sK9(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
        & ( sP2(sK9(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP2(X4,X2,X1,X0) )
            & ( sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f106,plain,(
    ! [X2,X0,X1] : sP3(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f85,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f91])).

% (15838)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f87,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f88,f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP3(X0,X1,X2,X3) )
      & ( sP3(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP3(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f24,f29,f28])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f387,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f385,f113])).

fof(f113,plain,
    ( ~ r2_hidden(sK5,sK4)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f385,plain,
    ( r2_hidden(sK5,sK4)
    | spl10_1 ),
    inference(resolution,[],[f99,f154])).

fof(f154,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
    | spl10_1 ),
    inference(resolution,[],[f147,f148])).

fof(f148,plain,
    ( ~ r1_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f137,plain,
    ( sK4 != k5_xboole_0(sK4,k1_xboole_0)
    | ~ r1_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | spl10_1 ),
    inference(superposition,[],[f110,f125])).

fof(f110,plain,
    ( sK4 != k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f147,plain,(
    ! [X14,X13] :
      ( r1_xboole_0(X14,X13)
      | ~ r1_xboole_0(X13,X14) ) ),
    inference(forward_demodulation,[],[f136,f56])).

fof(f136,plain,(
    ! [X14,X13] :
      ( r1_xboole_0(k5_xboole_0(X14,k1_xboole_0),X13)
      | ~ r1_xboole_0(X13,X14) ) ),
    inference(superposition,[],[f121,f125])).

fof(f121,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f98,f60])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f95])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f93])).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f152,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f121,f141])).

fof(f141,plain,
    ( ! [X4,X5] : ~ r1_xboole_0(X4,X5)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl10_3
  <=> ! [X5,X4] : ~ r1_xboole_0(X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f145,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f138,f143,f140])).

fof(f138,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r1_xboole_0(X4,X5)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f64,f125])).

fof(f116,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f97,f112,f108])).

% (15826)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f97,plain,
    ( ~ r2_hidden(sK5,sK4)
    | sK4 = k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(definition_unfolding,[],[f54,f62,f95])).

fof(f54,plain,
    ( ~ r2_hidden(sK5,sK4)
    | sK4 = k4_xboole_0(sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( r2_hidden(sK5,sK4)
      | sK4 != k4_xboole_0(sK4,k1_tarski(sK5)) )
    & ( ~ r2_hidden(sK5,sK4)
      | sK4 = k4_xboole_0(sK4,k1_tarski(sK5)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK5,sK4)
        | sK4 != k4_xboole_0(sK4,k1_tarski(sK5)) )
      & ( ~ r2_hidden(sK5,sK4)
        | sK4 = k4_xboole_0(sK4,k1_tarski(sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f115,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f96,f112,f108])).

fof(f96,plain,
    ( r2_hidden(sK5,sK4)
    | sK4 != k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(definition_unfolding,[],[f55,f62,f95])).

fof(f55,plain,
    ( r2_hidden(sK5,sK4)
    | sK4 != k4_xboole_0(sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:02:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (15823)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.44  % (15831)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.47  % (15831)Refutation not found, incomplete strategy% (15831)------------------------------
% 0.19/0.47  % (15831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (15831)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (15831)Memory used [KB]: 10618
% 0.19/0.47  % (15831)Time elapsed: 0.099 s
% 0.19/0.47  % (15831)------------------------------
% 0.19/0.47  % (15831)------------------------------
% 0.19/0.48  % (15848)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.49  % (15850)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.49  % (15835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (15829)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (15821)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (15822)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (15824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (15822)Refutation not found, incomplete strategy% (15822)------------------------------
% 0.19/0.50  % (15822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (15822)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (15822)Memory used [KB]: 10746
% 0.19/0.50  % (15822)Time elapsed: 0.103 s
% 0.19/0.50  % (15822)------------------------------
% 0.19/0.50  % (15822)------------------------------
% 0.19/0.50  % (15828)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (15848)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (15828)Refutation not found, incomplete strategy% (15828)------------------------------
% 0.19/0.50  % (15828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f590,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f115,f116,f145,f152,f387,f589])).
% 0.19/0.51  fof(f589,plain,(
% 0.19/0.51    ~spl10_1 | ~spl10_2 | ~spl10_4),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f588])).
% 0.19/0.51  fof(f588,plain,(
% 0.19/0.51    $false | (~spl10_1 | ~spl10_2 | ~spl10_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f582,f114])).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    r2_hidden(sK5,sK4) | ~spl10_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f112])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    spl10_2 <=> r2_hidden(sK5,sK4)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.19/0.51  fof(f582,plain,(
% 0.19/0.51    ~r2_hidden(sK5,sK4) | (~spl10_1 | ~spl10_4)),
% 0.19/0.51    inference(resolution,[],[f578,f105])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    ( ! [X2,X3,X1] : (sP2(X3,X1,X2,X3)) )),
% 0.19/0.51    inference(equality_resolution,[],[f82])).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | X0 != X3) )),
% 0.19/0.51    inference(cnf_transformation,[],[f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP2(X0,X1,X2,X3)))),
% 0.19/0.51    inference(rectify,[],[f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP2(X4,X2,X1,X0)))),
% 0.19/0.51    inference(flattening,[],[f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP2(X4,X2,X1,X0)))),
% 0.19/0.51    inference(nnf_transformation,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X4,X2,X1,X0] : (sP2(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 0.19/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.19/0.51  fof(f578,plain,(
% 0.19/0.51    ( ! [X0] : (~sP2(X0,sK5,sK5,sK5) | ~r2_hidden(X0,sK4)) ) | (~spl10_1 | ~spl10_4)),
% 0.19/0.51    inference(resolution,[],[f342,f554])).
% 0.19/0.51  fof(f554,plain,(
% 0.19/0.51    ( ! [X40] : (~r2_hidden(X40,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | ~r2_hidden(X40,sK4)) ) | (~spl10_1 | ~spl10_4)),
% 0.19/0.51    inference(resolution,[],[f286,f392])).
% 0.19/0.51  fof(f392,plain,(
% 0.19/0.51    r1_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | ~spl10_1),
% 0.19/0.51    inference(superposition,[],[f98,f109])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    sK4 = k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | ~spl10_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f108])).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    spl10_1 <=> sK4 = k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f59,f62])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.19/0.51  fof(f286,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) ) | ~spl10_4),
% 0.19/0.51    inference(resolution,[],[f279,f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.19/0.51    inference(rectify,[],[f43])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.19/0.51    inference(flattening,[],[f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.19/0.51    inference(nnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.19/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.51  fof(f279,plain,(
% 0.19/0.51    ( ! [X6,X8,X7] : (~sP0(X6,X7,X8) | ~r1_xboole_0(X6,X8)) ) | ~spl10_4),
% 0.19/0.51    inference(subsumption_resolution,[],[f276,f144])).
% 0.19/0.51  fof(f144,plain,(
% 0.19/0.51    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) ) | ~spl10_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f143])).
% 0.19/0.51  fof(f143,plain,(
% 0.19/0.51    spl10_4 <=> ! [X6] : ~r2_hidden(X6,k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.19/0.51  fof(f276,plain,(
% 0.19/0.51    ( ! [X6,X8,X7] : (~sP0(X6,X7,X8) | r2_hidden(X7,k1_xboole_0) | ~r1_xboole_0(X6,X8)) )),
% 0.19/0.51    inference(resolution,[],[f68,f135])).
% 0.19/0.51  fof(f135,plain,(
% 0.19/0.51    ( ! [X12,X11] : (sP1(X12,X11,k1_xboole_0) | ~r1_xboole_0(X11,X12)) )),
% 0.19/0.51    inference(superposition,[],[f117,f125])).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(resolution,[],[f64,f58])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.51    inference(rectify,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X1,X0))) )),
% 0.19/0.51    inference(superposition,[],[f102,f60])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 0.19/0.51    inference(equality_resolution,[],[f74])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.19/0.51    inference(cnf_transformation,[],[f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.19/0.51    inference(nnf_transformation,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.19/0.51    inference(definition_folding,[],[f2,f26,f25])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.19/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.19/0.51    inference(rectify,[],[f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.19/0.51    inference(nnf_transformation,[],[f26])).
% 0.19/0.51  fof(f342,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP2(X0,X1,X2,X3)) )),
% 0.19/0.51    inference(resolution,[],[f106,f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3) | ~sP2(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f49])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ((~sP2(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP2(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ! [X3,X2,X1,X0] : (? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP2(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP2(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.19/0.51    inference(rectify,[],[f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP2(X4,X2,X1,X0)) & (sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.19/0.51    inference(nnf_transformation,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (sP3(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP2(X4,X2,X1,X0)))),
% 0.19/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 0.19/0.51    inference(equality_resolution,[],[f101])).
% 0.19/0.51  fof(f101,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.19/0.51    inference(definition_unfolding,[],[f85,f93])).
% 0.19/0.51  fof(f93,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f66,f92])).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f76,f91])).
% 0.19/0.51  % (15838)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  fof(f91,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f87,f90])).
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f88,f89])).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.51    inference(cnf_transformation,[],[f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) & (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.51    inference(nnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X0,X1,X2,X3))),
% 0.19/0.51    inference(definition_folding,[],[f24,f29,f28])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.19/0.51  fof(f387,plain,(
% 0.19/0.51    spl10_1 | spl10_2),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f386])).
% 0.19/0.51  fof(f386,plain,(
% 0.19/0.51    $false | (spl10_1 | spl10_2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f385,f113])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    ~r2_hidden(sK5,sK4) | spl10_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f112])).
% 0.19/0.51  fof(f385,plain,(
% 0.19/0.51    r2_hidden(sK5,sK4) | spl10_1),
% 0.19/0.51    inference(resolution,[],[f99,f154])).
% 0.19/0.51  fof(f154,plain,(
% 0.19/0.51    ~r1_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) | spl10_1),
% 0.19/0.51    inference(resolution,[],[f147,f148])).
% 0.19/0.51  fof(f148,plain,(
% 0.19/0.51    ~r1_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | spl10_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f137,f56])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.19/0.51  fof(f137,plain,(
% 0.19/0.51    sK4 != k5_xboole_0(sK4,k1_xboole_0) | ~r1_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | spl10_1),
% 0.19/0.51    inference(superposition,[],[f110,f125])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    sK4 != k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) | spl10_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f108])).
% 0.19/0.51  fof(f147,plain,(
% 0.19/0.51    ( ! [X14,X13] : (r1_xboole_0(X14,X13) | ~r1_xboole_0(X13,X14)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f136,f56])).
% 0.19/0.51  fof(f136,plain,(
% 0.19/0.51    ( ! [X14,X13] : (r1_xboole_0(k5_xboole_0(X14,k1_xboole_0),X13) | ~r1_xboole_0(X13,X14)) )),
% 0.19/0.51    inference(superposition,[],[f121,f125])).
% 0.19/0.51  fof(f121,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1)) )),
% 0.19/0.51    inference(superposition,[],[f98,f60])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f65,f95])).
% 0.19/0.51  fof(f95,plain,(
% 0.19/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f57,f94])).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f61,f93])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,axiom,(
% 0.19/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.19/0.51  fof(f152,plain,(
% 0.19/0.51    ~spl10_3),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f150])).
% 0.19/0.51  fof(f150,plain,(
% 0.19/0.51    $false | ~spl10_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f121,f141])).
% 0.19/0.51  fof(f141,plain,(
% 0.19/0.51    ( ! [X4,X5] : (~r1_xboole_0(X4,X5)) ) | ~spl10_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f140])).
% 0.19/0.51  fof(f140,plain,(
% 0.19/0.51    spl10_3 <=> ! [X5,X4] : ~r1_xboole_0(X4,X5)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.19/0.51  fof(f145,plain,(
% 0.19/0.51    spl10_3 | spl10_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f138,f143,f140])).
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    ( ! [X6,X4,X5] : (~r2_hidden(X6,k1_xboole_0) | ~r1_xboole_0(X4,X5)) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f132])).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    ( ! [X6,X4,X5] : (~r2_hidden(X6,k1_xboole_0) | ~r1_xboole_0(X4,X5) | ~r1_xboole_0(X4,X5)) )),
% 0.19/0.51    inference(superposition,[],[f64,f125])).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    spl10_1 | ~spl10_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f97,f112,f108])).
% 0.19/0.51  % (15826)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  fof(f97,plain,(
% 0.19/0.51    ~r2_hidden(sK5,sK4) | sK4 = k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),
% 0.19/0.51    inference(definition_unfolding,[],[f54,f62,f95])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ~r2_hidden(sK5,sK4) | sK4 = k4_xboole_0(sK4,k1_tarski(sK5))),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    (r2_hidden(sK5,sK4) | sK4 != k4_xboole_0(sK4,k1_tarski(sK5))) & (~r2_hidden(sK5,sK4) | sK4 = k4_xboole_0(sK4,k1_tarski(sK5)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK5,sK4) | sK4 != k4_xboole_0(sK4,k1_tarski(sK5))) & (~r2_hidden(sK5,sK4) | sK4 = k4_xboole_0(sK4,k1_tarski(sK5))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 0.19/0.51    inference(nnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.51    inference(negated_conjecture,[],[f17])).
% 0.19/0.51  fof(f17,conjecture,(
% 0.19/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.19/0.51  fof(f115,plain,(
% 0.19/0.51    ~spl10_1 | spl10_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f96,f112,f108])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    r2_hidden(sK5,sK4) | sK4 != k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),
% 0.19/0.51    inference(definition_unfolding,[],[f55,f62,f95])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    r2_hidden(sK5,sK4) | sK4 != k4_xboole_0(sK4,k1_tarski(sK5))),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (15848)------------------------------
% 0.19/0.51  % (15848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15848)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (15848)Memory used [KB]: 6396
% 0.19/0.51  % (15848)Time elapsed: 0.127 s
% 0.19/0.51  % (15848)------------------------------
% 0.19/0.51  % (15848)------------------------------
% 0.19/0.51  % (15819)Success in time 0.167 s
%------------------------------------------------------------------------------

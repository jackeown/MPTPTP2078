%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:58 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 345 expanded)
%              Number of leaves         :   27 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  301 ( 572 expanded)
%              Number of equality atoms :  180 ( 428 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f148,f204,f209,f276,f345,f351])).

fof(f351,plain,
    ( spl5_1
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | spl5_1
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f98,f344,f214])).

fof(f214,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))
        | sK2 = X8 )
    | ~ spl5_6 ),
    inference(superposition,[],[f90,f183])).

fof(f183,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl5_6
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f90,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f344,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl5_12
  <=> r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f98,plain,
    ( sK1 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f345,plain,
    ( spl5_12
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f340,f273,f181,f342])).

fof(f273,plain,
    ( spl5_10
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f340,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(superposition,[],[f333,f275])).

fof(f275,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f273])).

fof(f333,plain,
    ( ! [X4] : r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,X4))
    | ~ spl5_6 ),
    inference(resolution,[],[f310,f91])).

fof(f91,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
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
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f32])).

% (30762)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (30761)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f32,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f310,plain,
    ( ! [X40] : sP0(X40,sK2,sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,X40))
    | ~ spl5_6 ),
    inference(superposition,[],[f94,f231])).

fof(f231,plain,
    ( ! [X46] : k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X46) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,X46)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f227,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f65,f69,f64,f75])).

% (30745)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f227,plain,
    ( ! [X46] : k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X46) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(X46,X46,X46,X46,X46,X46,X46,X46),k3_xboole_0(k6_enumset1(X46,X46,X46,X46,X46,X46,X46,X46),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))))
    | ~ spl5_6 ),
    inference(superposition,[],[f77,f183])).

fof(f94,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

% (30764)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f276,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f265,f206,f273])).

fof(f206,plain,
    ( spl5_7
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f265,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f264,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f264,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f261,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f261,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl5_7 ),
    inference(superposition,[],[f77,f208])).

fof(f208,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f206])).

fof(f209,plain,
    ( spl5_7
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f179,f145,f101,f206])).

fof(f101,plain,
    ( spl5_2
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f145,plain,
    ( spl5_3
  <=> k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f179,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f103,f162])).

fof(f162,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)
    | ~ spl5_3 ),
    inference(superposition,[],[f147,f40])).

% (30743)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f147,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f103,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f204,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f163,f145,f181])).

fof(f163,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)
    | ~ spl5_3 ),
    inference(superposition,[],[f40,f147])).

fof(f148,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f115,f101,f145])).

fof(f115,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f114,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f50,f72,f72])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f114,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f111,f39])).

fof(f111,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl5_2 ),
    inference(superposition,[],[f77,f103])).

fof(f104,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f78,f101])).

fof(f78,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f37,f75,f75,f75])).

fof(f37,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f99,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f96])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (30759)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (30759)Refutation not found, incomplete strategy% (30759)------------------------------
% 0.22/0.53  % (30759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30759)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30759)Memory used [KB]: 1791
% 0.22/0.53  % (30759)Time elapsed: 0.109 s
% 0.22/0.53  % (30759)------------------------------
% 0.22/0.53  % (30759)------------------------------
% 0.22/0.54  % (30768)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (30769)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (30768)Refutation not found, incomplete strategy% (30768)------------------------------
% 0.22/0.54  % (30768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30768)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30768)Memory used [KB]: 6268
% 0.22/0.54  % (30768)Time elapsed: 0.119 s
% 0.22/0.54  % (30768)------------------------------
% 0.22/0.54  % (30768)------------------------------
% 0.22/0.54  % (30769)Refutation not found, incomplete strategy% (30769)------------------------------
% 0.22/0.54  % (30769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30769)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30769)Memory used [KB]: 6268
% 0.22/0.54  % (30769)Time elapsed: 0.127 s
% 0.22/0.54  % (30769)------------------------------
% 0.22/0.54  % (30769)------------------------------
% 1.52/0.57  % (30758)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.58  % (30751)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.52/0.58  % (30741)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.52/0.58  % (30741)Refutation not found, incomplete strategy% (30741)------------------------------
% 1.52/0.58  % (30741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (30741)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.58  
% 1.52/0.58  % (30741)Memory used [KB]: 1663
% 1.52/0.58  % (30741)Time elapsed: 0.139 s
% 1.52/0.58  % (30741)------------------------------
% 1.52/0.58  % (30741)------------------------------
% 1.68/0.60  % (30740)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.68/0.60  % (30744)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.68/0.61  % (30748)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.68/0.61  % (30749)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.68/0.62  % (30752)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.68/0.62  % (30750)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.68/0.62  % (30751)Refutation found. Thanks to Tanya!
% 1.68/0.62  % SZS status Theorem for theBenchmark
% 1.68/0.62  % (30754)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.68/0.62  % SZS output start Proof for theBenchmark
% 1.68/0.62  fof(f354,plain,(
% 1.68/0.62    $false),
% 1.68/0.62    inference(avatar_sat_refutation,[],[f99,f104,f148,f204,f209,f276,f345,f351])).
% 1.68/0.62  fof(f351,plain,(
% 1.68/0.62    spl5_1 | ~spl5_6 | ~spl5_12),
% 1.68/0.62    inference(avatar_contradiction_clause,[],[f346])).
% 1.68/0.62  fof(f346,plain,(
% 1.68/0.62    $false | (spl5_1 | ~spl5_6 | ~spl5_12)),
% 1.68/0.62    inference(unit_resulting_resolution,[],[f98,f344,f214])).
% 1.68/0.62  fof(f214,plain,(
% 1.68/0.62    ( ! [X8] : (~r2_hidden(X8,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)) | sK2 = X8) ) | ~spl5_6),
% 1.68/0.62    inference(superposition,[],[f90,f183])).
% 1.68/0.62  fof(f183,plain,(
% 1.68/0.62    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) | ~spl5_6),
% 1.68/0.62    inference(avatar_component_clause,[],[f181])).
% 1.68/0.62  fof(f181,plain,(
% 1.68/0.62    spl5_6 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)),
% 1.68/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.68/0.62  fof(f90,plain,(
% 1.68/0.62    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.68/0.62    inference(equality_resolution,[],[f82])).
% 1.68/0.62  fof(f82,plain,(
% 1.68/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.68/0.62    inference(definition_unfolding,[],[f45,f75])).
% 1.68/0.62  fof(f75,plain,(
% 1.68/0.62    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.68/0.62    inference(definition_unfolding,[],[f41,f74])).
% 1.68/0.62  fof(f74,plain,(
% 1.68/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.68/0.62    inference(definition_unfolding,[],[f42,f73])).
% 1.68/0.62  fof(f73,plain,(
% 1.68/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.68/0.62    inference(definition_unfolding,[],[f49,f72])).
% 1.68/0.62  fof(f72,plain,(
% 1.68/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.68/0.62    inference(definition_unfolding,[],[f51,f71])).
% 1.68/0.62  fof(f71,plain,(
% 1.68/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.68/0.62    inference(definition_unfolding,[],[f62,f70])).
% 1.68/0.63  fof(f70,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f63,f64])).
% 1.68/0.63  fof(f64,plain,(
% 1.68/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f18])).
% 1.68/0.63  fof(f18,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.68/0.63  fof(f63,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f17])).
% 1.68/0.63  fof(f17,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.68/0.63  fof(f62,plain,(
% 1.68/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f16])).
% 1.68/0.63  fof(f16,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.68/0.63  fof(f51,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f15])).
% 1.68/0.63  fof(f15,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.68/0.63  fof(f49,plain,(
% 1.68/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f14])).
% 1.68/0.63  fof(f14,axiom,(
% 1.68/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.68/0.63  fof(f42,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f13])).
% 1.68/0.63  fof(f13,axiom,(
% 1.68/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.63  fof(f41,plain,(
% 1.68/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f12])).
% 1.68/0.63  fof(f12,axiom,(
% 1.68/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.63  fof(f45,plain,(
% 1.68/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.68/0.63    inference(cnf_transformation,[],[f30])).
% 1.68/0.63  fof(f30,plain,(
% 1.68/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.68/0.63  fof(f29,plain,(
% 1.68/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f28,plain,(
% 1.68/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.68/0.63    inference(rectify,[],[f27])).
% 1.68/0.63  fof(f27,plain,(
% 1.68/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.68/0.63    inference(nnf_transformation,[],[f6])).
% 1.68/0.63  fof(f6,axiom,(
% 1.68/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.68/0.63  fof(f344,plain,(
% 1.68/0.63    r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)) | ~spl5_12),
% 1.68/0.63    inference(avatar_component_clause,[],[f342])).
% 1.68/0.63  fof(f342,plain,(
% 1.68/0.63    spl5_12 <=> r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.68/0.63  fof(f98,plain,(
% 1.68/0.63    sK1 != sK2 | spl5_1),
% 1.68/0.63    inference(avatar_component_clause,[],[f96])).
% 1.68/0.63  fof(f96,plain,(
% 1.68/0.63    spl5_1 <=> sK1 = sK2),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.68/0.63  fof(f345,plain,(
% 1.68/0.63    spl5_12 | ~spl5_6 | ~spl5_10),
% 1.68/0.63    inference(avatar_split_clause,[],[f340,f273,f181,f342])).
% 1.68/0.63  fof(f273,plain,(
% 1.68/0.63    spl5_10 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.68/0.63  fof(f340,plain,(
% 1.68/0.63    r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)) | (~spl5_6 | ~spl5_10)),
% 1.68/0.63    inference(superposition,[],[f333,f275])).
% 1.68/0.63  fof(f275,plain,(
% 1.68/0.63    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1) | ~spl5_10),
% 1.68/0.63    inference(avatar_component_clause,[],[f273])).
% 1.68/0.63  fof(f333,plain,(
% 1.68/0.63    ( ! [X4] : (r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,X4))) ) | ~spl5_6),
% 1.68/0.63    inference(resolution,[],[f310,f91])).
% 1.68/0.63  fof(f91,plain,(
% 1.68/0.63    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.68/0.63    inference(equality_resolution,[],[f55])).
% 1.68/0.63  fof(f55,plain,(
% 1.68/0.63    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f35])).
% 1.68/0.63  fof(f35,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.68/0.63  fof(f34,plain,(
% 1.68/0.63    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f33,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.68/0.63    inference(rectify,[],[f32])).
% 1.68/0.63  % (30762)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.68/0.63  % (30761)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.68/0.63  fof(f32,plain,(
% 1.68/0.63    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.68/0.63    inference(flattening,[],[f31])).
% 1.68/0.63  fof(f31,plain,(
% 1.68/0.63    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.68/0.63    inference(nnf_transformation,[],[f23])).
% 1.68/0.63  fof(f23,plain,(
% 1.68/0.63    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.68/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.68/0.63  fof(f310,plain,(
% 1.68/0.63    ( ! [X40] : (sP0(X40,sK2,sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,X40))) ) | ~spl5_6),
% 1.68/0.63    inference(superposition,[],[f94,f231])).
% 1.68/0.63  fof(f231,plain,(
% 1.68/0.63    ( ! [X46] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X46) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,X46)) ) | ~spl5_6),
% 1.68/0.63    inference(forward_demodulation,[],[f227,f77])).
% 1.68/0.63  fof(f77,plain,(
% 1.68/0.63    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 1.68/0.63    inference(definition_unfolding,[],[f65,f69,f64,f75])).
% 1.68/0.63  % (30745)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.68/0.63  fof(f69,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.68/0.63    inference(definition_unfolding,[],[f44,f43])).
% 1.68/0.63  fof(f43,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f1])).
% 1.68/0.63  fof(f1,axiom,(
% 1.68/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.68/0.63  fof(f44,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f4])).
% 1.68/0.63  fof(f4,axiom,(
% 1.68/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.68/0.63  fof(f65,plain,(
% 1.68/0.63    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f11])).
% 1.68/0.63  fof(f11,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 1.68/0.63  fof(f227,plain,(
% 1.68/0.63    ( ! [X46] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X46) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(X46,X46,X46,X46,X46,X46,X46,X46),k3_xboole_0(k6_enumset1(X46,X46,X46,X46,X46,X46,X46,X46),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))))) ) | ~spl5_6),
% 1.68/0.63    inference(superposition,[],[f77,f183])).
% 1.68/0.63  fof(f94,plain,(
% 1.68/0.63    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.68/0.63    inference(equality_resolution,[],[f85])).
% 1.68/0.63  fof(f85,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.68/0.63    inference(definition_unfolding,[],[f60,f73])).
% 1.68/0.63  fof(f60,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.68/0.63    inference(cnf_transformation,[],[f36])).
% 1.68/0.63  fof(f36,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.68/0.63    inference(nnf_transformation,[],[f24])).
% 1.68/0.63  fof(f24,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.68/0.63    inference(definition_folding,[],[f22,f23])).
% 1.68/0.63  fof(f22,plain,(
% 1.68/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.68/0.63    inference(ennf_transformation,[],[f5])).
% 1.68/0.63  % (30764)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.68/0.63  fof(f5,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.68/0.63  fof(f276,plain,(
% 1.68/0.63    spl5_10 | ~spl5_7),
% 1.68/0.63    inference(avatar_split_clause,[],[f265,f206,f273])).
% 1.68/0.63  fof(f206,plain,(
% 1.68/0.63    spl5_7 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.68/0.63  fof(f265,plain,(
% 1.68/0.63    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1) | ~spl5_7),
% 1.68/0.63    inference(forward_demodulation,[],[f264,f40])).
% 1.68/0.63  fof(f40,plain,(
% 1.68/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.63    inference(cnf_transformation,[],[f2])).
% 1.68/0.63  fof(f2,axiom,(
% 1.68/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.68/0.63  fof(f264,plain,(
% 1.68/0.63    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1) | ~spl5_7),
% 1.68/0.63    inference(forward_demodulation,[],[f261,f39])).
% 1.68/0.63  fof(f39,plain,(
% 1.68/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f3])).
% 1.68/0.63  fof(f3,axiom,(
% 1.68/0.63    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.68/0.63  fof(f261,plain,(
% 1.68/0.63    k6_enumset1(sK1,sK1,sK1,sK1,sK2,sK2,sK2,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl5_7),
% 1.68/0.63    inference(superposition,[],[f77,f208])).
% 1.68/0.63  fof(f208,plain,(
% 1.68/0.63    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)) | ~spl5_7),
% 1.68/0.63    inference(avatar_component_clause,[],[f206])).
% 1.68/0.63  fof(f209,plain,(
% 1.68/0.63    spl5_7 | ~spl5_2 | ~spl5_3),
% 1.68/0.63    inference(avatar_split_clause,[],[f179,f145,f101,f206])).
% 1.68/0.63  fof(f101,plain,(
% 1.68/0.63    spl5_2 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.68/0.63  fof(f145,plain,(
% 1.68/0.63    spl5_3 <=> k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.68/0.63  fof(f179,plain,(
% 1.68/0.63    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2)) | (~spl5_2 | ~spl5_3)),
% 1.68/0.63    inference(backward_demodulation,[],[f103,f162])).
% 1.68/0.63  fof(f162,plain,(
% 1.68/0.63    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) | ~spl5_3),
% 1.68/0.63    inference(superposition,[],[f147,f40])).
% 1.68/0.63  % (30743)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.68/0.63  fof(f147,plain,(
% 1.68/0.63    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) | ~spl5_3),
% 1.68/0.63    inference(avatar_component_clause,[],[f145])).
% 1.68/0.63  fof(f103,plain,(
% 1.68/0.63    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_2),
% 1.68/0.63    inference(avatar_component_clause,[],[f101])).
% 1.68/0.63  fof(f204,plain,(
% 1.68/0.63    spl5_6 | ~spl5_3),
% 1.68/0.63    inference(avatar_split_clause,[],[f163,f145,f181])).
% 1.68/0.63  fof(f163,plain,(
% 1.68/0.63    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) | ~spl5_3),
% 1.68/0.63    inference(superposition,[],[f40,f147])).
% 1.68/0.63  fof(f148,plain,(
% 1.68/0.63    spl5_3 | ~spl5_2),
% 1.68/0.63    inference(avatar_split_clause,[],[f115,f101,f145])).
% 1.68/0.63  fof(f115,plain,(
% 1.68/0.63    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK2,sK2) | ~spl5_2),
% 1.68/0.63    inference(forward_demodulation,[],[f114,f83])).
% 1.68/0.63  fof(f83,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f50,f72,f72])).
% 1.68/0.63  fof(f50,plain,(
% 1.68/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f7])).
% 1.68/0.63  fof(f7,axiom,(
% 1.68/0.63    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 1.68/0.63  fof(f114,plain,(
% 1.68/0.63    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) | ~spl5_2),
% 1.68/0.63    inference(forward_demodulation,[],[f111,f39])).
% 1.68/0.63  fof(f111,plain,(
% 1.68/0.63    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl5_2),
% 1.68/0.63    inference(superposition,[],[f77,f103])).
% 1.68/0.63  fof(f104,plain,(
% 1.68/0.63    spl5_2),
% 1.68/0.63    inference(avatar_split_clause,[],[f78,f101])).
% 1.68/0.63  fof(f78,plain,(
% 1.68/0.63    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.68/0.63    inference(definition_unfolding,[],[f37,f75,f75,f75])).
% 1.68/0.63  fof(f37,plain,(
% 1.68/0.63    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.68/0.63    inference(cnf_transformation,[],[f26])).
% 1.68/0.63  fof(f26,plain,(
% 1.68/0.63    sK1 != sK2 & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.68/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f25])).
% 1.68/0.63  fof(f25,plain,(
% 1.68/0.63    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.68/0.63    introduced(choice_axiom,[])).
% 1.68/0.63  fof(f21,plain,(
% 1.68/0.63    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.68/0.63    inference(ennf_transformation,[],[f20])).
% 1.68/0.63  fof(f20,negated_conjecture,(
% 1.68/0.63    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.68/0.63    inference(negated_conjecture,[],[f19])).
% 1.68/0.63  fof(f19,conjecture,(
% 1.68/0.63    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.68/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.68/0.63  fof(f99,plain,(
% 1.68/0.63    ~spl5_1),
% 1.68/0.63    inference(avatar_split_clause,[],[f38,f96])).
% 1.68/0.63  fof(f38,plain,(
% 1.68/0.63    sK1 != sK2),
% 1.68/0.63    inference(cnf_transformation,[],[f26])).
% 1.68/0.63  % SZS output end Proof for theBenchmark
% 1.68/0.63  % (30751)------------------------------
% 1.68/0.63  % (30751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  % (30751)Termination reason: Refutation
% 1.68/0.63  
% 1.68/0.63  % (30751)Memory used [KB]: 11129
% 1.68/0.63  % (30751)Time elapsed: 0.187 s
% 1.68/0.63  % (30751)------------------------------
% 1.68/0.63  % (30751)------------------------------
% 1.68/0.63  % (30772)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.68/0.63  % (30771)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.68/0.63  % (30773)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.68/0.63  % (30773)Refutation not found, incomplete strategy% (30773)------------------------------
% 1.68/0.63  % (30773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  % (30773)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.63  
% 1.68/0.63  % (30773)Memory used [KB]: 1663
% 1.68/0.63  % (30773)Time elapsed: 0.002 s
% 1.68/0.63  % (30773)------------------------------
% 1.68/0.63  % (30773)------------------------------
% 1.68/0.63  % (30771)Refutation not found, incomplete strategy% (30771)------------------------------
% 1.68/0.63  % (30771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  % (30771)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.63  
% 1.68/0.63  % (30771)Memory used [KB]: 6268
% 1.68/0.63  % (30771)Time elapsed: 0.167 s
% 1.68/0.63  % (30771)------------------------------
% 1.68/0.63  % (30771)------------------------------
% 1.68/0.63  % (30757)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.68/0.64  % (30736)Success in time 0.269 s
%------------------------------------------------------------------------------

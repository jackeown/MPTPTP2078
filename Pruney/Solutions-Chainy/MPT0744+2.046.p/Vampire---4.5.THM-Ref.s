%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 411 expanded)
%              Number of leaves         :   34 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  434 (1093 expanded)
%              Number of equality atoms :   46 ( 216 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f639,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f116,f161,f163,f227,f232,f253,f259,f260,f292,f294,f499,f539,f638])).

fof(f638,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f622,f101])).

fof(f101,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f58,f98])).

fof(f98,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f61,f96,f97])).

fof(f97,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f78,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f87,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f88,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f89,f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f69,f95])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f61,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f58,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f622,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f110,f142])).

fof(f142,plain,
    ( sK1 = sK2
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f110,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_1
  <=> r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f539,plain,
    ( spl5_13
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | spl5_13
    | ~ spl5_33 ),
    inference(resolution,[],[f531,f224])).

fof(f224,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl5_13
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f531,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_33 ),
    inference(resolution,[],[f119,f498])).

fof(f498,plain,
    ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl5_33
  <=> r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f71,f102])).

fof(f102,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f59,f97])).

fof(f59,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f499,plain,
    ( spl5_9
    | spl5_33
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f491,f108,f496,f168])).

fof(f168,plain,
    ( spl5_9
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f491,plain,
    ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f304,f106])).

fof(f106,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f85,f96])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f304,plain,
    ( ! [X0,X1] :
        ( ~ sP0(X1,X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
        | r2_hidden(sK1,X1)
        | r2_hidden(sK1,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f109,f79])).

% (14548)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (14547)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (14544)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f109,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f294,plain,
    ( ~ spl5_13
    | spl5_5
    | spl5_9
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f254,f243,f168,f140,f222])).

fof(f243,plain,
    ( spl5_14
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f254,plain,
    ( r2_hidden(sK1,sK2)
    | sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f244,f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v1_ordinal1(X1)
      | r2_hidden(X1,sK2)
      | sK2 = X1
      | ~ r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f118,f55])).

fof(f55,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r1_ordinal1(sK1,sK2)
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( r1_ordinal1(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK1,X1)
            | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK1,X1)
            | r2_hidden(sK1,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK1,X1)
          | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK1,X1)
          | r2_hidden(sK1,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK1,sK2)
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( r1_ordinal1(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | ~ v1_ordinal1(X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f62,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f244,plain,
    ( v1_ordinal1(sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f292,plain,
    ( spl5_1
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl5_1
    | ~ spl5_9 ),
    inference(resolution,[],[f270,f110])).

fof(f270,plain,
    ( ! [X0] : r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))
    | ~ spl5_9 ),
    inference(resolution,[],[f266,f106])).

fof(f266,plain,
    ( ! [X4,X5] :
        ( ~ sP0(X5,sK2,X4)
        | r2_hidden(sK1,X4) )
    | ~ spl5_9 ),
    inference(resolution,[],[f170,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f170,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f260,plain,
    ( ~ spl5_11
    | ~ spl5_9
    | spl5_13 ),
    inference(avatar_split_clause,[],[f257,f222,f168,f214])).

fof(f214,plain,
    ( spl5_11
  <=> v1_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f257,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v1_ordinal1(sK2)
    | spl5_13 ),
    inference(resolution,[],[f224,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f259,plain,
    ( ~ spl5_7
    | ~ spl5_6
    | ~ spl5_2
    | spl5_13 ),
    inference(avatar_split_clause,[],[f256,f222,f112,f148,f152])).

fof(f152,plain,
    ( spl5_7
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f148,plain,
    ( spl5_6
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f112,plain,
    ( spl5_2
  <=> r1_ordinal1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f256,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1)
    | spl5_13 ),
    inference(resolution,[],[f224,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

% (14556)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f253,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f252])).

% (14562)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f252,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f251,f54])).

fof(f54,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f251,plain,
    ( ~ v3_ordinal1(sK1)
    | spl5_14 ),
    inference(resolution,[],[f245,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f245,plain,
    ( ~ v1_ordinal1(sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f232,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f230,f55])).

fof(f230,plain,
    ( ~ v3_ordinal1(sK2)
    | spl5_11 ),
    inference(resolution,[],[f216,f63])).

fof(f216,plain,
    ( ~ v1_ordinal1(sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f214])).

fof(f227,plain,
    ( ~ spl5_7
    | ~ spl5_6
    | ~ spl5_13
    | spl5_2 ),
    inference(avatar_split_clause,[],[f180,f112,f222,f148,f152])).

fof(f180,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1)
    | spl5_2 ),
    inference(resolution,[],[f114,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f114,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f163,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f154,f54])).

fof(f154,plain,
    ( ~ v3_ordinal1(sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f161,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f150,f55])).

fof(f150,plain,
    ( ~ v3_ordinal1(sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f116,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f100,f112,f108])).

fof(f100,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f56,f98])).

fof(f56,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f115,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f99,f112,f108])).

fof(f99,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f57,f98])).

% (14552)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f57,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14551)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.47  % (14558)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (14549)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (14566)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (14542)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (14538)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (14557)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (14541)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (14543)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (14539)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (14540)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (14563)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (14537)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (14549)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f639,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f115,f116,f161,f163,f227,f232,f253,f259,f260,f292,f294,f499,f539,f638])).
% 0.20/0.53  fof(f638,plain,(
% 0.20/0.53    spl5_1 | ~spl5_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f637])).
% 0.20/0.53  fof(f637,plain,(
% 0.20/0.53    $false | (spl5_1 | ~spl5_5)),
% 0.20/0.53    inference(resolution,[],[f622,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f58,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f61,f96,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f60,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f70,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f78,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f87,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f88,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f89,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f69,f95])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.53  fof(f622,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | (spl5_1 | ~spl5_5)),
% 0.20/0.53    inference(forward_demodulation,[],[f110,f142])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    sK1 = sK2 | ~spl5_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f140])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    spl5_5 <=> sK1 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | spl5_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    spl5_1 <=> r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.53  fof(f539,plain,(
% 0.20/0.53    spl5_13 | ~spl5_33),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f532])).
% 0.20/0.53  fof(f532,plain,(
% 0.20/0.53    $false | (spl5_13 | ~spl5_33)),
% 0.20/0.53    inference(resolution,[],[f531,f224])).
% 0.20/0.53  fof(f224,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK2) | spl5_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f222])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    spl5_13 <=> r1_tarski(sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.53  fof(f531,plain,(
% 0.20/0.53    r1_tarski(sK1,sK2) | ~spl5_33),
% 0.20/0.53    inference(resolution,[],[f119,f498])).
% 0.20/0.53  fof(f498,plain,(
% 0.20/0.53    r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_33),
% 0.20/0.53    inference(avatar_component_clause,[],[f496])).
% 0.20/0.53  fof(f496,plain,(
% 0.20/0.53    spl5_33 <=> r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | r1_tarski(X1,X0)) )),
% 0.20/0.53    inference(superposition,[],[f71,f102])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f59,f97])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.53  fof(f499,plain,(
% 0.20/0.53    spl5_9 | spl5_33 | ~spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f491,f108,f496,f168])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    spl5_9 <=> r2_hidden(sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.53  fof(f491,plain,(
% 0.20/0.53    r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK1,sK2) | ~spl5_1),
% 0.20/0.53    inference(resolution,[],[f304,f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.53    inference(definition_unfolding,[],[f85,f96])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.53    inference(definition_folding,[],[f1,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.53  fof(f304,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~sP0(X1,X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r2_hidden(sK1,X1) | r2_hidden(sK1,X0)) ) | ~spl5_1),
% 0.20/0.53    inference(resolution,[],[f109,f79])).
% 0.20/0.53  % (14548)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (14547)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (14544)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.54    inference(rectify,[],[f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.54    inference(flattening,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.54    inference(nnf_transformation,[],[f34])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl5_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f108])).
% 0.20/0.54  fof(f294,plain,(
% 0.20/0.54    ~spl5_13 | spl5_5 | spl5_9 | ~spl5_14),
% 0.20/0.54    inference(avatar_split_clause,[],[f254,f243,f168,f140,f222])).
% 0.20/0.54  fof(f243,plain,(
% 0.20/0.54    spl5_14 <=> v1_ordinal1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.54  fof(f254,plain,(
% 0.20/0.54    r2_hidden(sK1,sK2) | sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl5_14),
% 0.20/0.54    inference(resolution,[],[f244,f122])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X1] : (~v1_ordinal1(X1) | r2_hidden(X1,sK2) | sK2 = X1 | ~r1_tarski(X1,sK2)) )),
% 0.20/0.54    inference(resolution,[],[f118,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    v3_ordinal1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.54    inference(flattening,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.54    inference(negated_conjecture,[],[f21])).
% 0.20/0.54  fof(f21,conjecture,(
% 0.20/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | r2_hidden(X0,X1) | ~v1_ordinal1(X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f62,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.54    inference(flattening,[],[f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.20/0.54  fof(f244,plain,(
% 0.20/0.54    v1_ordinal1(sK1) | ~spl5_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f243])).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    spl5_1 | ~spl5_9),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f286])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    $false | (spl5_1 | ~spl5_9)),
% 0.20/0.54    inference(resolution,[],[f270,f110])).
% 0.20/0.54  fof(f270,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) ) | ~spl5_9),
% 0.20/0.54    inference(resolution,[],[f266,f106])).
% 0.20/0.54  fof(f266,plain,(
% 0.20/0.54    ( ! [X4,X5] : (~sP0(X5,sK2,X4) | r2_hidden(sK1,X4)) ) | ~spl5_9),
% 0.20/0.54    inference(resolution,[],[f170,f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    r2_hidden(sK1,sK2) | ~spl5_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f168])).
% 0.20/0.54  fof(f260,plain,(
% 0.20/0.54    ~spl5_11 | ~spl5_9 | spl5_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f257,f222,f168,f214])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    spl5_11 <=> v1_ordinal1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.54  fof(f257,plain,(
% 0.20/0.54    ~r2_hidden(sK1,sK2) | ~v1_ordinal1(sK2) | spl5_13),
% 0.20/0.54    inference(resolution,[],[f224,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.20/0.54    inference(rectify,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.20/0.54  fof(f259,plain,(
% 0.20/0.54    ~spl5_7 | ~spl5_6 | ~spl5_2 | spl5_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f256,f222,f112,f148,f152])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    spl5_7 <=> v3_ordinal1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    spl5_6 <=> v3_ordinal1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    spl5_2 <=> r1_ordinal1(sK1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.54  fof(f256,plain,(
% 0.20/0.54    ~r1_ordinal1(sK1,sK2) | ~v3_ordinal1(sK2) | ~v3_ordinal1(sK1) | spl5_13),
% 0.20/0.54    inference(resolution,[],[f224,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.54    inference(flattening,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.54  % (14556)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  fof(f253,plain,(
% 0.20/0.54    spl5_14),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f252])).
% 0.20/0.54  % (14562)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  fof(f252,plain,(
% 0.20/0.54    $false | spl5_14),
% 0.20/0.54    inference(resolution,[],[f251,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    v3_ordinal1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f251,plain,(
% 0.20/0.54    ~v3_ordinal1(sK1) | spl5_14),
% 0.20/0.54    inference(resolution,[],[f245,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.20/0.54  fof(f245,plain,(
% 0.20/0.54    ~v1_ordinal1(sK1) | spl5_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f243])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    spl5_11),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.54  fof(f231,plain,(
% 0.20/0.54    $false | spl5_11),
% 0.20/0.54    inference(resolution,[],[f230,f55])).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    ~v3_ordinal1(sK2) | spl5_11),
% 0.20/0.54    inference(resolution,[],[f216,f63])).
% 0.20/0.54  fof(f216,plain,(
% 0.20/0.54    ~v1_ordinal1(sK2) | spl5_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f214])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    ~spl5_7 | ~spl5_6 | ~spl5_13 | spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f180,f112,f222,f148,f152])).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    ~r1_tarski(sK1,sK2) | ~v3_ordinal1(sK2) | ~v3_ordinal1(sK1) | spl5_2),
% 0.20/0.54    inference(resolution,[],[f114,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ~r1_ordinal1(sK1,sK2) | spl5_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f112])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    spl5_7),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f162])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    $false | spl5_7),
% 0.20/0.54    inference(resolution,[],[f154,f54])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    ~v3_ordinal1(sK1) | spl5_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f152])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    spl5_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    $false | spl5_6),
% 0.20/0.54    inference(resolution,[],[f150,f55])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ~v3_ordinal1(sK2) | spl5_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f148])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    spl5_1 | spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f100,f112,f108])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.20/0.54    inference(definition_unfolding,[],[f56,f98])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    ~spl5_1 | ~spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f99,f112,f108])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 0.20/0.54    inference(definition_unfolding,[],[f57,f98])).
% 0.20/0.54  % (14552)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (14549)------------------------------
% 0.20/0.54  % (14549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14549)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (14549)Memory used [KB]: 6524
% 0.20/0.54  % (14549)Time elapsed: 0.110 s
% 0.20/0.54  % (14549)------------------------------
% 0.20/0.54  % (14549)------------------------------
% 0.20/0.54  % (14536)Success in time 0.184 s
%------------------------------------------------------------------------------

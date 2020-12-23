%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 180 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  287 ( 496 expanded)
%              Number of equality atoms :   40 ( 104 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30754)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f86,f89,f134,f142,f262,f267,f273,f275])).

fof(f275,plain,
    ( spl3_2
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f68,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl3_7 ),
    inference(resolution,[],[f133,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f133,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_7
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f68,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f273,plain,
    ( spl3_1
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl3_1
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f271,f64])).

fof(f64,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f271,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl3_15 ),
    inference(resolution,[],[f261,f45])).

fof(f261,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl3_15
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f267,plain,
    ( ~ spl3_3
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl3_3
    | spl3_13 ),
    inference(subsumption_resolution,[],[f265,f81])).

fof(f81,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f265,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_13 ),
    inference(subsumption_resolution,[],[f263,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f263,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl3_13 ),
    inference(resolution,[],[f252,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f252,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_13
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f262,plain,
    ( spl3_15
    | ~ spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f257,f80,f250,f259])).

fof(f257,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f245,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f245,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_3 ),
    inference(superposition,[],[f48,f240])).

fof(f240,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f103,f39])).

fof(f103,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X2)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f100,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f94,f81])).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f47,f42])).

fof(f42,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f99,f41])).

fof(f99,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1,X0),X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f142,plain,
    ( ~ spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f140,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f138,f81])).

fof(f138,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(resolution,[],[f124,f52])).

fof(f124,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_5
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f134,plain,
    ( spl3_7
    | ~ spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f129,f84,f122,f131])).

fof(f84,plain,
    ( spl3_4
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f129,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f116,f41])).

fof(f116,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(superposition,[],[f49,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(resolution,[],[f102,f39])).

fof(f102,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f100,f85])).

fof(f85,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f89,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_3 ),
    inference(resolution,[],[f82,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f82,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f78,f84,f80])).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f43])).

fof(f43,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f69,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f40,f66,f62])).

fof(f40,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (30776)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (30756)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (30770)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (30770)Refutation not found, incomplete strategy% (30770)------------------------------
% 0.20/0.51  % (30770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30756)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (30770)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30770)Memory used [KB]: 10618
% 0.20/0.51  % (30770)Time elapsed: 0.005 s
% 0.20/0.51  % (30770)------------------------------
% 0.20/0.51  % (30770)------------------------------
% 0.20/0.51  % (30764)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (30754)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f69,f86,f89,f134,f142,f262,f267,f273,f275])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    spl3_2 | ~spl3_7),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f274])).
% 0.20/0.51  fof(f274,plain,(
% 0.20/0.51    $false | (spl3_2 | ~spl3_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f68,f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl3_7),
% 0.20/0.51    inference(resolution,[],[f133,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl3_7 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl3_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f273,plain,(
% 0.20/0.51    spl3_1 | ~spl3_15),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f272])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    $false | (spl3_1 | ~spl3_15)),
% 0.20/0.51    inference(subsumption_resolution,[],[f271,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl3_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl3_15),
% 0.20/0.51    inference(resolution,[],[f261,f45])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f259])).
% 0.20/0.51  fof(f259,plain,(
% 0.20/0.51    spl3_15 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.51  fof(f267,plain,(
% 0.20/0.51    ~spl3_3 | spl3_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    $false | (~spl3_3 | spl3_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f265,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    v1_relat_1(k1_xboole_0) | ~spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl3_3 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    ~v1_relat_1(k1_xboole_0) | spl3_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f263,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.51  fof(f263,plain,(
% 0.20/0.51    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl3_13),
% 0.20/0.51    inference(resolution,[],[f252,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl3_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f250])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    spl3_13 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    spl3_15 | ~spl3_13 | ~spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f257,f80,f250,f259])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f245,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_3),
% 0.20/0.51    inference(superposition,[],[f48,f240])).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl3_3),
% 0.20/0.51    inference(resolution,[],[f103,f39])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X2] : (~v1_relat_1(X2) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X2))) ) | ~spl3_3),
% 0.20/0.51    inference(resolution,[],[f100,f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f81])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.51    inference(superposition,[],[f47,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(resolution,[],[f99,f41])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_xboole_0(X2) | X1 = X2 | ~r1_tarski(X1,X2)) )),
% 0.20/0.51    inference(resolution,[],[f74,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(rectify,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X1,X0),X1) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(resolution,[],[f55,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ~spl3_3 | spl3_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    $false | (~spl3_3 | spl3_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f140,f39])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    ~v1_relat_1(sK0) | (~spl3_3 | spl3_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f138,f81])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl3_5),
% 0.20/0.51    inference(resolution,[],[f124,f52])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl3_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl3_5 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl3_7 | ~spl3_5 | ~spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f129,f84,f122,f131])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl3_4 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f116,f41])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_4),
% 0.20/0.51    inference(superposition,[],[f49,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl3_4),
% 0.20/0.51    inference(resolution,[],[f102,f39])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ) | ~spl3_4),
% 0.20/0.51    inference(resolution,[],[f100,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f84])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl3_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    $false | spl3_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f87,f41])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | spl3_3),
% 0.20/0.51    inference(resolution,[],[f82,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ~v1_relat_1(k1_xboole_0) | spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ~spl3_3 | spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f78,f84,f80])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(superposition,[],[f46,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ~spl3_1 | ~spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f66,f62])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (30756)------------------------------
% 0.20/0.51  % (30756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30756)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (30756)Memory used [KB]: 10746
% 0.20/0.51  % (30756)Time elapsed: 0.078 s
% 0.20/0.51  % (30756)------------------------------
% 0.20/0.51  % (30756)------------------------------
% 0.20/0.52  % (30750)Success in time 0.162 s
%------------------------------------------------------------------------------

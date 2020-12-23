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
% DateTime   : Thu Dec  3 12:48:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 273 expanded)
%              Number of leaves         :   28 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 ( 416 expanded)
%              Number of equality atoms :   55 ( 185 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f851,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f90,f95,f113,f139,f164,f264,f305,f431,f628,f648,f850])).

fof(f850,plain,
    ( spl3_1
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f849,f426,f295,f64])).

fof(f64,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f295,plain,
    ( spl3_23
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f426,plain,
    ( spl3_28
  <=> k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f849,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f848,f326])).

fof(f326,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f175,f306])).

fof(f306,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f196,f165])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

% (14059)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f60,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f196,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f190,f174])).

fof(f174,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f60,f61])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f190,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f62,f61])).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f54,f57])).

% (14060)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f175,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f61,f58])).

fof(f848,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f847,f165])).

fof(f847,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f428,f297])).

fof(f297,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f295])).

fof(f428,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f426])).

fof(f648,plain,
    ( ~ spl3_4
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f89,f627,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
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

fof(f627,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl3_29
  <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f628,plain,
    ( spl3_29
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f623,f155,f133,f625])).

fof(f133,plain,
    ( spl3_9
  <=> r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f155,plain,
    ( spl3_12
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f623,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f135,f157])).

fof(f157,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f135,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f431,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f430,f155,f87,f426])).

fof(f430,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f421,f157])).

fof(f421,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | ~ spl3_4 ),
    inference(resolution,[],[f209,f89])).

fof(f209,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(resolution,[],[f206,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f206,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(forward_demodulation,[],[f59,f61])).

fof(f59,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f39,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f305,plain,
    ( spl3_23
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f283,f260,f295])).

fof(f260,plain,
    ( spl3_19
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f283,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_19 ),
    inference(resolution,[],[f262,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f262,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f260])).

fof(f264,plain,
    ( spl3_19
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f256,f137,f260])).

fof(f137,plain,
    ( spl3_10
  <=> ! [X2] : ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f256,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(resolution,[],[f138,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f138,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f164,plain,
    ( spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f148,f97,f155])).

fof(f97,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f148,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_5 ),
    inference(resolution,[],[f99,f41])).

fof(f99,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f139,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f131,f82,f137,f133])).

fof(f82,plain,
    ( spl3_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f131,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(k1_xboole_0))
        | r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f53,f84])).

fof(f84,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK2(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f34])).

fof(f34,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK2(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f113,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f112,f97])).

% (14061)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f112,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f77,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(unit_resulting_resolution,[],[f37,f41])).

fof(f37,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f77,plain,(
    ! [X0] : v1_xboole_0(k1_relat_1(k1_subset_1(X0))) ),
    inference(unit_resulting_resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f95,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f87,f82])).

fof(f93,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f89,f40])).

fof(f90,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f80,f87])).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f37,f69])).

fof(f67,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f64])).

fof(f36,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f18])).

fof(f18,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 09:54:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.46  % (14072)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.46  % (14063)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.48  % (14062)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (14071)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.48  % (14063)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f851,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f67,f90,f95,f113,f139,f164,f264,f305,f431,f628,f648,f850])).
% 0.23/0.49  fof(f850,plain,(
% 0.23/0.49    spl3_1 | ~spl3_23 | ~spl3_28),
% 0.23/0.49    inference(avatar_split_clause,[],[f849,f426,f295,f64])).
% 0.23/0.49  fof(f64,plain,(
% 0.23/0.49    spl3_1 <=> k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.49  fof(f295,plain,(
% 0.23/0.49    spl3_23 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.23/0.49  fof(f426,plain,(
% 0.23/0.49    spl3_28 <=> k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.23/0.49  fof(f849,plain,(
% 0.23/0.49    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl3_23 | ~spl3_28)),
% 0.23/0.49    inference(forward_demodulation,[],[f848,f326])).
% 0.23/0.49  fof(f326,plain,(
% 0.23/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.49    inference(backward_demodulation,[],[f175,f306])).
% 0.23/0.49  fof(f306,plain,(
% 0.23/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f196,f165])).
% 0.23/0.49  fof(f165,plain,(
% 0.23/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.49    inference(superposition,[],[f60,f58])).
% 0.23/0.49  fof(f58,plain,(
% 0.23/0.49    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.23/0.49    inference(definition_unfolding,[],[f38,f57])).
% 0.23/0.49  fof(f57,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f47,f56])).
% 0.23/0.49  fof(f56,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f49,f55])).
% 0.23/0.49  fof(f55,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).
% 0.23/0.49  fof(f49,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,axiom,(
% 0.23/0.49    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f11])).
% 0.23/0.49  fof(f11,axiom,(
% 0.23/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.49  fof(f38,plain,(
% 0.23/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  % (14059)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.49  fof(f60,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f45,f57])).
% 0.23/0.49  fof(f45,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.23/0.49  fof(f196,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 0.23/0.49    inference(superposition,[],[f190,f174])).
% 0.23/0.49  fof(f174,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.23/0.49    inference(backward_demodulation,[],[f60,f61])).
% 0.23/0.49  fof(f61,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f48,f57])).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,axiom,(
% 0.23/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.49  fof(f190,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f62,f61])).
% 0.23/0.49  fof(f62,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f54,f57])).
% 0.23/0.49  % (14060)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.23/0.49  fof(f175,plain,(
% 0.23/0.49    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.23/0.49    inference(superposition,[],[f61,f58])).
% 0.23/0.49  fof(f848,plain,(
% 0.23/0.49    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_23 | ~spl3_28)),
% 0.23/0.49    inference(forward_demodulation,[],[f847,f165])).
% 0.23/0.49  fof(f847,plain,(
% 0.23/0.49    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl3_23 | ~spl3_28)),
% 0.23/0.49    inference(forward_demodulation,[],[f428,f297])).
% 0.23/0.49  fof(f297,plain,(
% 0.23/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_23),
% 0.23/0.49    inference(avatar_component_clause,[],[f295])).
% 0.23/0.49  fof(f428,plain,(
% 0.23/0.49    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl3_28),
% 0.23/0.49    inference(avatar_component_clause,[],[f426])).
% 0.23/0.49  fof(f648,plain,(
% 0.23/0.49    ~spl3_4 | ~spl3_29),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f641])).
% 0.23/0.49  fof(f641,plain,(
% 0.23/0.49    $false | (~spl3_4 | ~spl3_29)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f89,f627,f43])).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f31])).
% 0.23/0.49  fof(f31,plain,(
% 0.23/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.49    inference(rectify,[],[f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.23/0.49    inference(nnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.23/0.49  fof(f627,plain,(
% 0.23/0.49    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~spl3_29),
% 0.23/0.49    inference(avatar_component_clause,[],[f625])).
% 0.23/0.49  fof(f625,plain,(
% 0.23/0.49    spl3_29 <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.23/0.49  fof(f89,plain,(
% 0.23/0.49    v1_xboole_0(k1_xboole_0) | ~spl3_4),
% 0.23/0.49    inference(avatar_component_clause,[],[f87])).
% 0.23/0.49  fof(f87,plain,(
% 0.23/0.49    spl3_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.49  fof(f628,plain,(
% 0.23/0.49    spl3_29 | ~spl3_9 | ~spl3_12),
% 0.23/0.49    inference(avatar_split_clause,[],[f623,f155,f133,f625])).
% 0.23/0.49  fof(f133,plain,(
% 0.23/0.49    spl3_9 <=> r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.49  fof(f155,plain,(
% 0.23/0.49    spl3_12 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.23/0.49  fof(f623,plain,(
% 0.23/0.49    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | (~spl3_9 | ~spl3_12)),
% 0.23/0.49    inference(forward_demodulation,[],[f135,f157])).
% 0.23/0.49  fof(f157,plain,(
% 0.23/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_12),
% 0.23/0.49    inference(avatar_component_clause,[],[f155])).
% 0.23/0.49  fof(f135,plain,(
% 0.23/0.49    r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~spl3_9),
% 0.23/0.49    inference(avatar_component_clause,[],[f133])).
% 0.23/0.49  fof(f431,plain,(
% 0.23/0.49    spl3_28 | ~spl3_4 | ~spl3_12),
% 0.23/0.49    inference(avatar_split_clause,[],[f430,f155,f87,f426])).
% 0.23/0.49  fof(f430,plain,(
% 0.23/0.49    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl3_4 | ~spl3_12)),
% 0.23/0.49    inference(forward_demodulation,[],[f421,f157])).
% 0.23/0.49  fof(f421,plain,(
% 0.23/0.49    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) | ~spl3_4),
% 0.23/0.49    inference(resolution,[],[f209,f89])).
% 0.23/0.49  fof(f209,plain,(
% 0.23/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.23/0.49    inference(resolution,[],[f206,f40])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.23/0.49  fof(f206,plain,(
% 0.23/0.49    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f59,f61])).
% 0.23/0.49  fof(f59,plain,(
% 0.23/0.49    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.23/0.49    inference(definition_unfolding,[],[f39,f57])).
% 0.23/0.49  fof(f39,plain,(
% 0.23/0.49    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f14])).
% 0.23/0.49  fof(f14,axiom,(
% 0.23/0.49    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.23/0.49  fof(f305,plain,(
% 0.23/0.49    spl3_23 | ~spl3_19),
% 0.23/0.49    inference(avatar_split_clause,[],[f283,f260,f295])).
% 0.23/0.49  fof(f260,plain,(
% 0.23/0.49    spl3_19 <=> v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.23/0.49  fof(f283,plain,(
% 0.23/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_19),
% 0.23/0.49    inference(resolution,[],[f262,f41])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.23/0.49  fof(f262,plain,(
% 0.23/0.49    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl3_19),
% 0.23/0.49    inference(avatar_component_clause,[],[f260])).
% 0.23/0.49  fof(f264,plain,(
% 0.23/0.49    spl3_19 | ~spl3_10),
% 0.23/0.49    inference(avatar_split_clause,[],[f256,f137,f260])).
% 0.23/0.49  fof(f137,plain,(
% 0.23/0.49    spl3_10 <=> ! [X2] : ~r2_hidden(X2,k2_relat_1(k1_xboole_0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.23/0.49  fof(f256,plain,(
% 0.23/0.49    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl3_10),
% 0.23/0.49    inference(resolution,[],[f138,f44])).
% 0.23/0.49  fof(f44,plain,(
% 0.23/0.49    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f31])).
% 0.23/0.49  fof(f138,plain,(
% 0.23/0.49    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0))) ) | ~spl3_10),
% 0.23/0.49    inference(avatar_component_clause,[],[f137])).
% 0.23/0.49  fof(f164,plain,(
% 0.23/0.49    spl3_12 | ~spl3_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f148,f97,f155])).
% 0.23/0.49  fof(f97,plain,(
% 0.23/0.49    spl3_5 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.49  fof(f148,plain,(
% 0.23/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_5),
% 0.23/0.49    inference(resolution,[],[f99,f41])).
% 0.23/0.49  fof(f99,plain,(
% 0.23/0.49    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl3_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f97])).
% 0.23/0.49  fof(f139,plain,(
% 0.23/0.49    spl3_9 | spl3_10 | ~spl3_3),
% 0.23/0.49    inference(avatar_split_clause,[],[f131,f82,f137,f133])).
% 0.23/0.49  fof(f82,plain,(
% 0.23/0.49    spl3_3 <=> v1_relat_1(k1_xboole_0)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.49  fof(f131,plain,(
% 0.23/0.49    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0)) | r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0))) ) | ~spl3_3),
% 0.23/0.49    inference(resolution,[],[f53,f84])).
% 0.23/0.49  fof(f84,plain,(
% 0.23/0.49    v1_relat_1(k1_xboole_0) | ~spl3_3),
% 0.23/0.49    inference(avatar_component_clause,[],[f82])).
% 0.23/0.49  fof(f53,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK2(X1),k1_relat_1(X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f35])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f34])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK2(X1),k1_relat_1(X1)))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(flattening,[],[f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f16])).
% 0.23/0.49  fof(f16,axiom,(
% 0.23/0.49    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.23/0.49  fof(f113,plain,(
% 0.23/0.49    spl3_5),
% 0.23/0.49    inference(avatar_split_clause,[],[f112,f97])).
% 0.23/0.49  % (14061)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.49  fof(f112,plain,(
% 0.23/0.49    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.23/0.49    inference(forward_demodulation,[],[f77,f69])).
% 0.23/0.49  fof(f69,plain,(
% 0.23/0.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f37,f41])).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f12,axiom,(
% 0.23/0.49    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    ( ! [X0] : (v1_xboole_0(k1_relat_1(k1_subset_1(X0)))) )),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f37,f42])).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,axiom,(
% 0.23/0.49    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.23/0.49  fof(f95,plain,(
% 0.23/0.49    spl3_3 | ~spl3_4),
% 0.23/0.49    inference(avatar_split_clause,[],[f93,f87,f82])).
% 0.23/0.49  fof(f93,plain,(
% 0.23/0.49    v1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f89,f40])).
% 0.23/0.49  fof(f90,plain,(
% 0.23/0.49    spl3_4),
% 0.23/0.49    inference(avatar_split_clause,[],[f80,f87])).
% 0.23/0.49  fof(f80,plain,(
% 0.23/0.49    v1_xboole_0(k1_xboole_0)),
% 0.23/0.49    inference(backward_demodulation,[],[f37,f69])).
% 0.23/0.49  fof(f67,plain,(
% 0.23/0.49    ~spl3_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f36,f64])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.23/0.49    inference(flattening,[],[f18])).
% 0.23/0.49  fof(f18,negated_conjecture,(
% 0.23/0.49    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.23/0.49    inference(negated_conjecture,[],[f17])).
% 0.23/0.49  fof(f17,conjecture,(
% 0.23/0.49    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (14063)------------------------------
% 0.23/0.49  % (14063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (14063)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (14063)Memory used [KB]: 6652
% 0.23/0.49  % (14063)Time elapsed: 0.024 s
% 0.23/0.49  % (14063)------------------------------
% 0.23/0.49  % (14063)------------------------------
% 0.23/0.49  % (14053)Success in time 0.117 s
%------------------------------------------------------------------------------

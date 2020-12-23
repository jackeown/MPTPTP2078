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
% DateTime   : Thu Dec  3 12:45:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 122 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  207 ( 304 expanded)
%              Number of equality atoms :   72 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f58,f66,f74,f82,f99,f114,f128,f161,f296,f310,f315])).

fof(f315,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f41,f311])).

fof(f311,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f302,f309])).

fof(f309,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl3_30
  <=> ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
        | k1_xboole_0 = k1_tarski(X0) )
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f297,f49])).

fof(f49,plain,
    ( ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_3
  <=> ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(k1_setfam_1(k1_tarski(X0)),X1)
        | k1_xboole_0 = k1_tarski(X0) )
    | ~ spl3_10
    | ~ spl3_28 ),
    inference(superposition,[],[f295,f81])).

fof(f81,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_10
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0)
        | k1_xboole_0 = X1 )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f41,plain,
    ( k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f310,plain,
    ( spl3_30
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f163,f159,f112,f97,f308])).

fof(f97,plain,
    ( spl3_12
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f112,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( r2_hidden(X1,X0)
        | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f159,plain,
    ( spl3_17
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f163,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f162,f98])).

fof(f98,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f162,plain,
    ( ! [X0] : k1_tarski(X0) != k3_xboole_0(k1_xboole_0,k1_tarski(X0))
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f160,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
        | r2_hidden(X1,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f160,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f296,plain,
    ( spl3_28
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f164,f159,f126,f112,f97,f48,f294])).

fof(f126,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0)
        | k1_xboole_0 = X1 )
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f135,f163])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0)
        | k1_xboole_0 = k1_tarski(X0)
        | k1_xboole_0 = X1 )
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(superposition,[],[f127,f49])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f161,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f106,f72,f64,f44,f159])).

fof(f44,plain,
    ( spl3_2
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f72,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f106,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f87,f100])).

fof(f100,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f45,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f45,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(superposition,[],[f65,f45])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f128,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f37,f126])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f114,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f34,f112])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f99,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f75,f56,f44,f97])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f57,f45])).

fof(f57,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f82,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f74,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f46,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (22660)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.46  % (22653)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (22657)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (22653)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (22658)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (22661)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f316,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f42,f46,f50,f58,f66,f74,f82,f99,f114,f128,f161,f296,f310,f315])).
% 0.22/0.47  fof(f315,plain,(
% 0.22/0.47    spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_28 | ~spl3_30),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f314])).
% 0.22/0.47  fof(f314,plain,(
% 0.22/0.47    $false | (spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_28 | ~spl3_30)),
% 0.22/0.47    inference(subsumption_resolution,[],[f41,f311])).
% 0.22/0.47  fof(f311,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | (~spl3_3 | ~spl3_10 | ~spl3_28 | ~spl3_30)),
% 0.22/0.47    inference(subsumption_resolution,[],[f302,f309])).
% 0.22/0.47  fof(f309,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | ~spl3_30),
% 0.22/0.47    inference(avatar_component_clause,[],[f308])).
% 0.22/0.47  fof(f308,plain,(
% 0.22/0.47    spl3_30 <=> ! [X0] : k1_xboole_0 != k1_tarski(X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.47  fof(f302,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) | k1_xboole_0 = k1_tarski(X0)) ) | (~spl3_3 | ~spl3_10 | ~spl3_28)),
% 0.22/0.47    inference(forward_demodulation,[],[f297,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) ) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl3_3 <=> ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f297,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(k1_setfam_1(k1_tarski(X0)),X1) | k1_xboole_0 = k1_tarski(X0)) ) | (~spl3_10 | ~spl3_28)),
% 0.22/0.47    inference(superposition,[],[f295,f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl3_10 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f295,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0) | k1_xboole_0 = X1) ) | ~spl3_28),
% 0.22/0.47    inference(avatar_component_clause,[],[f294])).
% 0.22/0.47  fof(f294,plain,(
% 0.22/0.47    spl3_28 <=> ! [X1,X0] : (k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0) | k1_xboole_0 = X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl3_1 <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f310,plain,(
% 0.22/0.47    spl3_30 | ~spl3_12 | ~spl3_14 | ~spl3_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f163,f159,f112,f97,f308])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    spl3_12 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    spl3_14 <=> ! [X1,X0] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.47  fof(f159,plain,(
% 0.22/0.47    spl3_17 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.47  fof(f163,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | (~spl3_12 | ~spl3_14 | ~spl3_17)),
% 0.22/0.47    inference(forward_demodulation,[],[f162,f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f97])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    ( ! [X0] : (k1_tarski(X0) != k3_xboole_0(k1_xboole_0,k1_tarski(X0))) ) | (~spl3_14 | ~spl3_17)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f160,f113])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) ) | ~spl3_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f112])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl3_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f159])).
% 0.22/0.47  fof(f296,plain,(
% 0.22/0.47    spl3_28 | ~spl3_3 | ~spl3_12 | ~spl3_14 | ~spl3_15 | ~spl3_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f164,f159,f126,f112,f97,f48,f294])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    spl3_15 <=> ! [X1,X0] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.47  fof(f164,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0) | k1_xboole_0 = X1) ) | (~spl3_3 | ~spl3_12 | ~spl3_14 | ~spl3_15 | ~spl3_17)),
% 0.22/0.47    inference(subsumption_resolution,[],[f135,f163])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X1,k1_tarski(X0))) = k3_xboole_0(k1_setfam_1(X1),X0) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = X1) ) | (~spl3_3 | ~spl3_15)),
% 0.22/0.47    inference(superposition,[],[f127,f49])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl3_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f126])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    spl3_17 | ~spl3_2 | ~spl3_7 | ~spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f106,f72,f64,f44,f159])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl3_2 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    spl3_7 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    spl3_9 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl3_2 | ~spl3_7 | ~spl3_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f87,f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl3_2 | ~spl3_9)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f45,f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f72])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f44])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl3_2 | ~spl3_7)),
% 0.22/0.47    inference(superposition,[],[f65,f45])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f64])).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    spl3_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f37,f126])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    spl3_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f112])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl3_12 | ~spl3_2 | ~spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f75,f56,f44,f97])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl3_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl3_2 | ~spl3_5)),
% 0.22/0.47    inference(superposition,[],[f57,f45])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f56])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f30,f80])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f36,f72])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f33,f64])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(rectify,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f56])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f48])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f44])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f39])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f12])).
% 0.22/0.47  fof(f12,conjecture,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (22653)------------------------------
% 0.22/0.47  % (22653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22653)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (22653)Memory used [KB]: 6268
% 0.22/0.47  % (22653)Time elapsed: 0.058 s
% 0.22/0.47  % (22653)------------------------------
% 0.22/0.47  % (22653)------------------------------
% 0.22/0.47  % (22648)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (22647)Success in time 0.113 s
%------------------------------------------------------------------------------

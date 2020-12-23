%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 122 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  186 ( 260 expanded)
%              Number of equality atoms :   59 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f60,f72,f76,f80,f88,f100,f108,f114,f124,f137,f141,f211,f215,f385,f411])).

fof(f411,plain,
    ( spl2_2
    | ~ spl2_14
    | ~ spl2_19
    | ~ spl2_24
    | ~ spl2_25
    | ~ spl2_35 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl2_2
    | ~ spl2_14
    | ~ spl2_19
    | ~ spl2_24
    | ~ spl2_25
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f55,f409])).

fof(f409,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_14
    | ~ spl2_19
    | ~ spl2_24
    | ~ spl2_25
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f391,f220])).

fof(f220,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_14
    | ~ spl2_19
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f217,f107])).

fof(f107,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl2_14
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f217,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_19
    | ~ spl2_25 ),
    inference(superposition,[],[f140,f214])).

fof(f214,plain,
    ( ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl2_25
  <=> ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f140,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f391,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl2_24
    | ~ spl2_35 ),
    inference(superposition,[],[f384,f210])).

fof(f210,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl2_24
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f384,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl2_35
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f55,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_2
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f385,plain,
    ( spl2_35
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f155,f135,f70,f383])).

fof(f70,plain,
    ( spl2_6
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f135,plain,
    ( spl2_18
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f155,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl2_6
    | ~ spl2_18 ),
    inference(superposition,[],[f136,f71])).

fof(f71,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f136,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f215,plain,
    ( spl2_25
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f133,f112,f78,f74,f213])).

fof(f74,plain,
    ( spl2_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f78,plain,
    ( spl2_8
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f112,plain,
    ( spl2_15
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f133,plain,
    ( ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6)
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f132,f75])).

fof(f75,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f132,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,k2_xboole_0(X6,X7)) = k5_xboole_0(X6,X6)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(superposition,[],[f113,f79])).

fof(f79,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f113,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f112])).

fof(f211,plain,
    ( spl2_24
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f184,f121,f98,f208])).

fof(f98,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f121,plain,
    ( spl2_16
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f184,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f123,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f123,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f121])).

fof(f141,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f42,f139])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f137,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f37,f135])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f124,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f109,f86,f48,f121])).

fof(f48,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f109,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f50,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f50,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f114,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f36,f112])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f108,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f101,f70,f58,f106])).

fof(f58,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f101,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f71,f59])).

fof(f59,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f100,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f38,f98])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f80,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f76,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f72,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f60,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f56,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f51,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (24341)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (24356)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (24346)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (24342)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (24350)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (24345)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (24347)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (24346)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f424,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f51,f56,f60,f72,f76,f80,f88,f100,f108,f114,f124,f137,f141,f211,f215,f385,f411])).
% 0.21/0.47  fof(f411,plain,(
% 0.21/0.47    spl2_2 | ~spl2_14 | ~spl2_19 | ~spl2_24 | ~spl2_25 | ~spl2_35),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.47  fof(f410,plain,(
% 0.21/0.47    $false | (spl2_2 | ~spl2_14 | ~spl2_19 | ~spl2_24 | ~spl2_25 | ~spl2_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f409])).
% 0.21/0.47  fof(f409,plain,(
% 0.21/0.47    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | (~spl2_14 | ~spl2_19 | ~spl2_24 | ~spl2_25 | ~spl2_35)),
% 0.21/0.47    inference(forward_demodulation,[],[f391,f220])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_14 | ~spl2_19 | ~spl2_25)),
% 0.21/0.47    inference(forward_demodulation,[],[f217,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl2_14 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | (~spl2_19 | ~spl2_25)),
% 0.21/0.47    inference(superposition,[],[f140,f214])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,X6)) ) | ~spl2_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f213])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    spl2_25 <=> ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl2_19 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.47  fof(f391,plain,(
% 0.21/0.47    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),sK1)) | (~spl2_24 | ~spl2_35)),
% 0.21/0.47    inference(superposition,[],[f384,f210])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~spl2_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f208])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    spl2_24 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.47  fof(f384,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | ~spl2_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f383])).
% 0.21/0.47  fof(f383,plain,(
% 0.21/0.47    spl2_35 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl2_2 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f385,plain,(
% 0.21/0.47    spl2_35 | ~spl2_6 | ~spl2_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f155,f135,f70,f383])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl2_6 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl2_18 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | (~spl2_6 | ~spl2_18)),
% 0.21/0.47    inference(superposition,[],[f136,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f70])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f135])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    spl2_25 | ~spl2_7 | ~spl2_8 | ~spl2_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f133,f112,f78,f74,f213])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl2_8 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl2_15 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,X6)) ) | (~spl2_7 | ~spl2_8 | ~spl2_15)),
% 0.21/0.47    inference(forward_demodulation,[],[f132,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ( ! [X6,X7] : (k4_xboole_0(X6,k2_xboole_0(X6,X7)) = k5_xboole_0(X6,X6)) ) | (~spl2_8 | ~spl2_15)),
% 0.21/0.47    inference(superposition,[],[f113,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f112])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    spl2_24 | ~spl2_13 | ~spl2_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f184,f121,f98,f208])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl2_13 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl2_16 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | (~spl2_13 | ~spl2_16)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f123,f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f121])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl2_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f139])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl2_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f135])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl2_16 | ~spl2_1 | ~spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f109,f86,f48,f121])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl2_10 <=> ! [X1,X0] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    r1_tarski(k1_tarski(sK0),sK1) | (~spl2_1 | ~spl2_10)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f50,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl2_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f112])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl2_14 | ~spl2_3 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f70,f58,f106])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_3 | ~spl2_6)),
% 0.21/0.47    inference(superposition,[],[f71,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl2_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f98])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f86])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f78])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f74])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f70])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f53])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.47    inference(negated_conjecture,[],[f19])).
% 0.21/0.47  fof(f19,conjecture,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f48])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24346)------------------------------
% 0.21/0.47  % (24346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24346)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24346)Memory used [KB]: 6396
% 0.21/0.47  % (24346)Time elapsed: 0.061 s
% 0.21/0.47  % (24346)------------------------------
% 0.21/0.47  % (24346)------------------------------
% 0.21/0.48  % (24348)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (24354)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (24357)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (24343)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (24355)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (24349)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (24340)Success in time 0.131 s
%------------------------------------------------------------------------------

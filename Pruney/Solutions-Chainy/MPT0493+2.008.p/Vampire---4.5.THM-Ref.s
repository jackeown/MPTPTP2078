%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  92 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  130 ( 218 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f53,f60,f65,f85,f93,f101])).

fof(f101,plain,
    ( ~ spl2_8
    | spl2_9
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl2_8
    | spl2_9
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f59,f97])).

fof(f97,plain,
    ( sK0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f64,f92])).

fof(f92,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_14
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f64,plain,
    ( sK0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_9
  <=> sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f59,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_8
  <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f93,plain,
    ( spl2_14
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f88,f83,f40,f91])).

fof(f40,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f83,plain,
    ( spl2_13
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f88,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(superposition,[],[f84,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f84,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f47,f40,f36,f83])).

fof(f36,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f47,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f41,f37])).

fof(f37,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f65,plain,
    ( ~ spl2_1
    | ~ spl2_9
    | spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f55,f51,f31,f62,f21])).

fof(f21,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f31,plain,
    ( spl2_3
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f51,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f55,plain,
    ( sK0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f33,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f33,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f60,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f49,f44,f26,f57])).

fof(f26,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f49,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f28,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f28,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f53,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f18,f51])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f46,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f42,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f34,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23387)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (23384)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (23385)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (23387)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (23394)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (23386)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (23389)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (23393)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (23392)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f53,f60,f65,f85,f93,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ~spl2_8 | spl2_9 | ~spl2_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    $false | (~spl2_8 | spl2_9 | ~spl2_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f59,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    sK0 != k3_xboole_0(sK0,k1_relat_1(sK1)) | (spl2_9 | ~spl2_14)),
% 0.21/0.50    inference(superposition,[],[f64,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl2_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl2_14 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    sK0 != k3_xboole_0(k1_relat_1(sK1),sK0) | spl2_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl2_9 <=> sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl2_8 <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl2_14 | ~spl2_5 | ~spl2_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f88,f83,f40,f91])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl2_13 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_5 | ~spl2_13)),
% 0.21/0.50    inference(superposition,[],[f84,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f40])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f83])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl2_13 | ~spl2_4 | ~spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f40,f36,f83])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    spl2_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.50    inference(superposition,[],[f41,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f36])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_9 | spl2_3 | ~spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f51,f31,f62,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    spl2_3 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl2_7 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    sK0 != k3_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | (spl2_3 | ~spl2_7)),
% 0.21/0.50    inference(superposition,[],[f33,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f51])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) | spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f31])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl2_8 | ~spl2_2 | ~spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f44,f26,f57])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    spl2_6 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | (~spl2_2 | ~spl2_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f28,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f44])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f26])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f51])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f40])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ~spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f13,f21])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (23387)------------------------------
% 0.21/0.50  % (23387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23387)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (23387)Memory used [KB]: 6140
% 0.21/0.50  % (23387)Time elapsed: 0.059 s
% 0.21/0.50  % (23387)------------------------------
% 0.21/0.50  % (23387)------------------------------
% 0.21/0.50  % (23393)Refutation not found, incomplete strategy% (23393)------------------------------
% 0.21/0.50  % (23393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23393)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23393)Memory used [KB]: 10618
% 0.21/0.50  % (23393)Time elapsed: 0.063 s
% 0.21/0.50  % (23393)------------------------------
% 0.21/0.50  % (23393)------------------------------
% 0.21/0.50  % (23381)Success in time 0.14 s
%------------------------------------------------------------------------------

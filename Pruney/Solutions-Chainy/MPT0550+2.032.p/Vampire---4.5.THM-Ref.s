%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  96 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :  160 ( 261 expanded)
%              Number of equality atoms :   39 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f33,f37,f41,f49,f53,f63,f71,f85,f91,f95,f102])).

fof(f102,plain,
    ( spl2_2
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl2_2
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f100,f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK0
    | spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f100,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_10
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f98,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f98,plain,
    ( sK0 = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(resolution,[],[f90,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f90,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_15
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f95,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f58,f47,f39,f93])).

fof(f39,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f47,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X1,X0) )
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f91,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f87,f83,f35,f89])).

fof(f35,plain,
    ( spl2_4
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f83,plain,
    ( spl2_14
  <=> ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 != k9_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f87,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f84,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f84,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f80,f69,f23,f83])).

fof(f23,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f69,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f80,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 != k9_relat_1(sK1,X0) )
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f70,f24])).

fof(f24,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f16,f69])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f63,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f59,f51,f31,f61])).

fof(f31,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f51,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f59,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f51])).

% (23186)Refutation not found, incomplete strategy% (23186)------------------------------
% (23186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f53,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f41,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f37,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f14,f35])).

fof(f14,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f33,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (23185)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (23186)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (23194)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (23193)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (23194)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f25,f29,f33,f37,f41,f49,f53,f63,f71,f85,f91,f95,f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl2_2 | ~spl2_10 | ~spl2_15 | ~spl2_16),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    $false | (spl2_2 | ~spl2_10 | ~spl2_15 | ~spl2_16)),
% 0.21/0.47    inference(subsumption_resolution,[],[f100,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k1_xboole_0 != sK0 | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    spl2_2 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | (~spl2_10 | ~spl2_15 | ~spl2_16)),
% 0.21/0.47    inference(forward_demodulation,[],[f98,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_10 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    sK0 = k4_xboole_0(sK0,k1_relat_1(sK1)) | (~spl2_15 | ~spl2_16)),
% 0.21/0.47    inference(resolution,[],[f90,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl2_16 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl2_15 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl2_16 | ~spl2_5 | ~spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f47,f39,f93])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl2_5 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl2_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X1,X0)) ) | (~spl2_5 | ~spl2_7)),
% 0.21/0.48    inference(resolution,[],[f48,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl2_15 | ~spl2_4 | ~spl2_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f87,f83,f35,f89])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl2_4 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl2_14 <=> ! [X0] : (r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 != k9_relat_1(sK1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_4 | ~spl2_14)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_4 | ~spl2_14)),
% 0.21/0.48    inference(superposition,[],[f84,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f35])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl2_14 | ~spl2_1 | ~spl2_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f69,f23,f83])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl2_12 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 != k9_relat_1(sK1,X0)) ) | (~spl2_1 | ~spl2_12)),
% 0.21/0.48    inference(resolution,[],[f70,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f23])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) ) | ~spl2_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl2_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f69])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl2_10 | ~spl2_3 | ~spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f59,f51,f31,f61])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl2_8 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) | (~spl2_3 | ~spl2_8)),
% 0.21/0.48    inference(resolution,[],[f52,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f31])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  % (23186)Refutation not found, incomplete strategy% (23186)------------------------------
% 0.21/0.48  % (23186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f35])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f31])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f27])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f23])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (23194)------------------------------
% 0.21/0.48  % (23194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23194)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (23194)Memory used [KB]: 10618
% 0.21/0.48  % (23194)Time elapsed: 0.064 s
% 0.21/0.48  % (23194)------------------------------
% 0.21/0.48  % (23194)------------------------------
% 0.21/0.48  % (23184)Success in time 0.122 s
%------------------------------------------------------------------------------

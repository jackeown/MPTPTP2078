%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 375 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f54,f58,f76,f83,f88,f95,f102])).

fof(f102,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f100,f26])).

fof(f26,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f100,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(resolution,[],[f94,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v5_relat_1(sK2,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f95,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f91,f86,f44,f34,f93])).

fof(f34,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( v5_relat_1(X1,X0)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( spl3_13
  <=> ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(k2_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v5_relat_1(sK2,X0) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f89,f36])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | v5_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f87,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(sK2),X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl3_13
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f84,f80,f56,f86])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f80,plain,
    ( spl3_12
  <=> sK0 = k2_xboole_0(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f57,f82])).

fof(f82,plain,
    ( sK0 = k2_xboole_0(k2_relat_1(sK2),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f83,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f78,f74,f34,f29,f80])).

fof(f29,plain,
    ( spl3_2
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,
    ( spl3_11
  <=> ! [X3,X2] :
        ( ~ v5_relat_1(X2,X3)
        | ~ v1_relat_1(X2)
        | k2_xboole_0(k2_relat_1(X2),X3) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f78,plain,
    ( sK0 = k2_xboole_0(k2_relat_1(sK2),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f77,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k2_xboole_0(k2_relat_1(sK2),sK0)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f75,f31])).

fof(f31,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f75,plain,
    ( ! [X2,X3] :
        ( ~ v5_relat_1(X2,X3)
        | ~ v1_relat_1(X2)
        | k2_xboole_0(k2_relat_1(X2),X3) = X3 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl3_11
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f71,f52,f48,f74])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f71,plain,
    ( ! [X2,X3] :
        ( ~ v5_relat_1(X2,X3)
        | ~ v1_relat_1(X2)
        | k2_xboole_0(k2_relat_1(X2),X3) = X3 )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v5_relat_1(sK2,sK1)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v5_relat_1(X2,X1)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v5_relat_1(X2,sK1)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ v5_relat_1(X2,sK1)
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ v5_relat_1(sK2,sK1)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v5_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f24])).

fof(f18,plain,(
    ~ v5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:47:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (28429)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (28423)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (28424)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (28429)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f54,f58,f76,f83,f88,f95,f102])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    spl3_1 | ~spl3_4 | ~spl3_14),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    $false | (spl3_1 | ~spl3_4 | ~spl3_14)),
% 0.22/0.44    inference(subsumption_resolution,[],[f100,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ~v5_relat_1(sK2,sK1) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    spl3_1 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    v5_relat_1(sK2,sK1) | (~spl3_4 | ~spl3_14)),
% 0.22/0.44    inference(resolution,[],[f94,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(sK0,X0) | v5_relat_1(sK2,X0)) ) | ~spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f93])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    spl3_14 <=> ! [X0] : (~r1_tarski(sK0,X0) | v5_relat_1(sK2,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    spl3_14 | ~spl3_3 | ~spl3_5 | ~spl3_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f91,f86,f44,f34,f93])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl3_5 <=> ! [X1,X0] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    spl3_13 <=> ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(k2_relat_1(sK2),X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(sK0,X0) | v5_relat_1(sK2,X0)) ) | (~spl3_3 | ~spl3_5 | ~spl3_13)),
% 0.22/0.44    inference(subsumption_resolution,[],[f89,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f34])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(sK0,X0) | v5_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | (~spl3_5 | ~spl3_13)),
% 0.22/0.44    inference(resolution,[],[f87,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f44])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(sK0,X0)) ) | ~spl3_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f86])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    spl3_13 | ~spl3_8 | ~spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f84,f80,f56,f86])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl3_8 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl3_12 <=> sK0 = k2_xboole_0(k2_relat_1(sK2),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl3_8 | ~spl3_12)),
% 0.22/0.44    inference(superposition,[],[f57,f82])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    sK0 = k2_xboole_0(k2_relat_1(sK2),sK0) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f80])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f56])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    spl3_12 | ~spl3_2 | ~spl3_3 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f78,f74,f34,f29,f80])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl3_2 <=> v5_relat_1(sK2,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl3_11 <=> ! [X3,X2] : (~v5_relat_1(X2,X3) | ~v1_relat_1(X2) | k2_xboole_0(k2_relat_1(X2),X3) = X3)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    sK0 = k2_xboole_0(k2_relat_1(sK2),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_11)),
% 0.22/0.44    inference(subsumption_resolution,[],[f77,f36])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ~v1_relat_1(sK2) | sK0 = k2_xboole_0(k2_relat_1(sK2),sK0) | (~spl3_2 | ~spl3_11)),
% 0.22/0.44    inference(resolution,[],[f75,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    v5_relat_1(sK2,sK0) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f29])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X2,X3] : (~v5_relat_1(X2,X3) | ~v1_relat_1(X2) | k2_xboole_0(k2_relat_1(X2),X3) = X3) ) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f74])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl3_11 | ~spl3_6 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f71,f52,f48,f74])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_6 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ( ! [X2,X3] : (~v5_relat_1(X2,X3) | ~v1_relat_1(X2) | k2_xboole_0(k2_relat_1(X2),X3) = X3) ) | (~spl3_6 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f49,f53])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f52])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f48])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f56])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f52])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f48])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(nnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f44])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f39])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    (~v5_relat_1(sK2,sK1) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1)) => (? [X2] : (~v5_relat_1(X2,sK1) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & r1_tarski(sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X2] : (~v5_relat_1(X2,sK1) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) => (~v5_relat_1(sK2,sK1) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & (v5_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f29])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    v5_relat_1(sK2,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f24])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ~v5_relat_1(sK2,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (28429)------------------------------
% 0.22/0.44  % (28429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (28429)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (28429)Memory used [KB]: 6140
% 0.22/0.44  % (28429)Time elapsed: 0.005 s
% 0.22/0.44  % (28429)------------------------------
% 0.22/0.44  % (28429)------------------------------
% 0.22/0.44  % (28415)Success in time 0.073 s
%------------------------------------------------------------------------------

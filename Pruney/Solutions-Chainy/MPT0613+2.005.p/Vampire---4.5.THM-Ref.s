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
% DateTime   : Thu Dec  3 12:51:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 120 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 370 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f54,f58,f74,f80,f87,f92,f98,f103])).

fof(f103,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f101,f36])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f101,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f99,f26])).

fof(f26,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f99,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f97,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( v4_relat_1(X1,X0)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f97,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_15
  <=> r1_tarski(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f98,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f93,f90,f39,f95])).

fof(f39,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f90,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f93,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(resolution,[],[f91,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl3_14
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f88,f84,f56,f90])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( spl3_13
  <=> sK0 = k2_xboole_0(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(superposition,[],[f57,f86])).

fof(f86,plain,
    ( sK0 = k2_xboole_0(k1_relat_1(sK2),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f87,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f82,f77,f52,f84])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f77,plain,
    ( spl3_12
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f82,plain,
    ( sK0 = k2_xboole_0(k1_relat_1(sK2),sK0)
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(resolution,[],[f79,f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f79,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f75,f72,f29,f77])).

fof(f29,plain,
    ( spl3_2
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f75,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f73,f31])).

fof(f31,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f70,f48,f34,f72])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f49,f36])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | r1_tarski(k1_relat_1(X1),X0) )
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
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v4_relat_1(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v4_relat_1(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v4_relat_1(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ v4_relat_1(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ v4_relat_1(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v4_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

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
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f24])).

fof(f18,plain,(
    ~ v4_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:31:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (7830)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (7828)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (7828)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f54,f58,f74,f80,f87,f92,f98,f103])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_15),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f101,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ~v1_relat_1(sK2) | (spl3_1 | ~spl3_5 | ~spl3_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f99,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ~v4_relat_1(sK2,sK1) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    spl3_1 <=> v4_relat_1(sK2,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    v4_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl3_5 | ~spl3_15)),
% 0.21/0.44    inference(resolution,[],[f97,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl3_5 <=> ! [X1,X0] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    r1_tarski(k1_relat_1(sK2),sK1) | ~spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f95])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl3_15 <=> r1_tarski(k1_relat_1(sK2),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    spl3_15 | ~spl3_4 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f93,f90,f39,f95])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    spl3_14 <=> ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(k1_relat_1(sK2),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    r1_tarski(k1_relat_1(sK2),sK1) | (~spl3_4 | ~spl3_14)),
% 0.21/0.44    inference(resolution,[],[f91,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f39])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f90])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl3_14 | ~spl3_8 | ~spl3_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f88,f84,f56,f90])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl3_8 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl3_13 <=> sK0 = k2_xboole_0(k1_relat_1(sK2),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(k1_relat_1(sK2),X0)) ) | (~spl3_8 | ~spl3_13)),
% 0.21/0.44    inference(superposition,[],[f57,f86])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    sK0 = k2_xboole_0(k1_relat_1(sK2),sK0) | ~spl3_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f84])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f56])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl3_13 | ~spl3_7 | ~spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f82,f77,f52,f84])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl3_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl3_12 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    sK0 = k2_xboole_0(k1_relat_1(sK2),sK0) | (~spl3_7 | ~spl3_12)),
% 0.21/0.44    inference(resolution,[],[f79,f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f52])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    spl3_12 | ~spl3_2 | ~spl3_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f72,f29,f77])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl3_2 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl3_11 <=> ! [X0] : (~v4_relat_1(sK2,X0) | r1_tarski(k1_relat_1(sK2),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_2 | ~spl3_11)),
% 0.21/0.44    inference(resolution,[],[f73,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    v4_relat_1(sK2,sK0) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f29])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_relat_1(sK2,X0) | r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl3_11 | ~spl3_3 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f70,f48,f34,f72])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl3_6 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_relat_1(sK2,X0) | r1_tarski(k1_relat_1(sK2),X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.21/0.44    inference(resolution,[],[f49,f36])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) ) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f48])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f56])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f52])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f48])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f44])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f39])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    (~v4_relat_1(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2)) & r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1)) => (? [X2] : (~v4_relat_1(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) & r1_tarski(sK0,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X2] : (~v4_relat_1(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) => (~v4_relat_1(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & (v4_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f29])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    v4_relat_1(sK2,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f24])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ~v4_relat_1(sK2,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (7828)------------------------------
% 0.21/0.44  % (7828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (7828)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (7828)Memory used [KB]: 10618
% 0.21/0.44  % (7828)Time elapsed: 0.005 s
% 0.21/0.44  % (7828)------------------------------
% 0.21/0.44  % (7828)------------------------------
% 0.21/0.44  % (7822)Success in time 0.078 s
%------------------------------------------------------------------------------

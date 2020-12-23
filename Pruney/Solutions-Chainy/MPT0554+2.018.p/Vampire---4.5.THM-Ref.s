%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 105 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 278 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f41,f45,f49,f53,f59,f80,f92,f110,f118])).

fof(f118,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_17 ),
    inference(subsumption_resolution,[],[f116,f36])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f116,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_4
    | spl3_17 ),
    inference(resolution,[],[f109,f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f109,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_17
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f110,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f105,f89,f57,f43,f24,f107])).

fof(f24,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f89,plain,
    ( spl3_14
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f105,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f104,f26])).

fof(f26,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f104,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f103,f58])).

fof(f58,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f103,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f101,f58])).

fof(f101,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(superposition,[],[f44,f91])).

fof(f91,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f92,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f85,f78,f29,f89])).

fof(f29,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f85,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f79,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f75,f51,f34,f78])).

fof(f51,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f59,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f54,f47,f34,f57])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f54,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f53,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f45,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f41,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f24])).

fof(f18,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:14:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (30754)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (30756)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (30754)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f27,f32,f37,f41,f45,f49,f53,f59,f80,f92,f110,f118])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ~spl3_3 | ~spl3_4 | spl3_17),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    $false | (~spl3_3 | ~spl3_4 | spl3_17)),
% 0.22/0.43    inference(subsumption_resolution,[],[f116,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f116,plain,(
% 0.22/0.43    ~v1_relat_1(sK2) | (~spl3_4 | spl3_17)),
% 0.22/0.43    inference(resolution,[],[f109,f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f109,plain,(
% 0.22/0.43    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_17),
% 0.22/0.43    inference(avatar_component_clause,[],[f107])).
% 0.22/0.43  fof(f107,plain,(
% 0.22/0.43    spl3_17 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    ~spl3_17 | spl3_1 | ~spl3_5 | ~spl3_8 | ~spl3_14),
% 0.22/0.43    inference(avatar_split_clause,[],[f105,f89,f57,f43,f24,f107])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl3_1 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl3_5 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl3_8 <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    spl3_14 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    ~v1_relat_1(k7_relat_1(sK2,sK1)) | (spl3_1 | ~spl3_5 | ~spl3_8 | ~spl3_14)),
% 0.22/0.43    inference(subsumption_resolution,[],[f104,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f24])).
% 0.22/0.43  fof(f104,plain,(
% 0.22/0.43    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl3_5 | ~spl3_8 | ~spl3_14)),
% 0.22/0.43    inference(forward_demodulation,[],[f103,f58])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f57])).
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k9_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl3_5 | ~spl3_8 | ~spl3_14)),
% 0.22/0.43    inference(forward_demodulation,[],[f101,f58])).
% 0.22/0.43  fof(f101,plain,(
% 0.22/0.43    r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k2_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl3_5 | ~spl3_14)),
% 0.22/0.43    inference(superposition,[],[f44,f91])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) | ~spl3_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f89])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f43])).
% 0.22/0.43  fof(f92,plain,(
% 0.22/0.43    spl3_14 | ~spl3_2 | ~spl3_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f85,f78,f29,f89])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    spl3_12 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) | (~spl3_2 | ~spl3_12)),
% 0.22/0.43    inference(resolution,[],[f79,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0)) ) | ~spl3_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f78])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    spl3_12 | ~spl3_3 | ~spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f75,f51,f34,f78])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl3_7 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0)) ) | (~spl3_3 | ~spl3_7)),
% 0.22/0.43    inference(resolution,[],[f52,f36])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) ) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f51])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl3_8 | ~spl3_3 | ~spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f54,f47,f34,f57])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    spl3_6 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.43    inference(resolution,[],[f48,f36])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f47])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f51])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f47])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f43])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f39])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f29])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    r1_tarski(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f24])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (30754)------------------------------
% 0.22/0.43  % (30754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (30754)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (30754)Memory used [KB]: 10618
% 0.22/0.43  % (30754)Time elapsed: 0.007 s
% 0.22/0.43  % (30754)------------------------------
% 0.22/0.43  % (30754)------------------------------
% 0.22/0.43  % (30747)Success in time 0.064 s
%------------------------------------------------------------------------------

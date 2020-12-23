%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  90 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  169 ( 264 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f59,f64,f79,f85,f89])).

fof(f89,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f86,f28])).

fof(f28,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f84,f38])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_13
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f85,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f81,f77,f45,f41,f83])).

fof(f41,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f45,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f77,plain,
    ( spl3_12
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f81,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(X0,sK0))
        | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),sK0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(X0,sK1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f75,f62,f49,f77])).

fof(f49,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f75,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),sK0) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f64,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f60,f57,f31,f62])).

fof(f31,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f60,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f58,f33])).

fof(f33,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f51,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f47,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

% (19952)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (19950)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (19950)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f59,f64,f79,f85,f89])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl3_1 | ~spl3_3 | ~spl3_13),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_3 | ~spl3_13)),
% 0.21/0.44    inference(subsumption_resolution,[],[f86,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    spl3_1 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl3_3 | ~spl3_13)),
% 0.21/0.44    inference(resolution,[],[f84,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1)) ) | ~spl3_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f83])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl3_13 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    spl3_13 | ~spl3_4 | ~spl3_5 | ~spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f81,f77,f45,f41,f83])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl3_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl3_12 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1) | ~v1_relat_1(X0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.21/0.44    inference(subsumption_resolution,[],[f80,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f41])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(k7_relat_1(X0,sK0)) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK0),sK1) | ~v1_relat_1(X0)) ) | (~spl3_5 | ~spl3_12)),
% 0.21/0.44    inference(resolution,[],[f78,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),sK0) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,sK1)) ) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl3_12 | ~spl3_6 | ~spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f62,f49,f77])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl3_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl3_9 <=> ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),sK0)) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.44    inference(resolution,[],[f50,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK0)) ) | ~spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) ) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl3_9 | ~spl3_2 | ~spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f60,f57,f31,f62])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl3_8 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK0)) ) | (~spl3_2 | ~spl3_8)),
% 0.21/0.44    inference(resolution,[],[f58,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f31])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f57])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.44  % (19952)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f41])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f36])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f31])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f26])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (19950)------------------------------
% 0.21/0.44  % (19950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (19950)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (19950)Memory used [KB]: 10618
% 0.21/0.44  % (19950)Time elapsed: 0.005 s
% 0.21/0.44  % (19950)------------------------------
% 0.21/0.44  % (19950)------------------------------
% 0.21/0.44  % (19944)Success in time 0.075 s
%------------------------------------------------------------------------------

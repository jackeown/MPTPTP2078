%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 108 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :  151 ( 225 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f36,f40,f44,f48,f52,f56,f80,f88,f115,f127,f140,f151,f160])).

fof(f160,plain,
    ( spl3_1
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_1
    | ~ spl3_24 ),
    inference(resolution,[],[f150,f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f150,plain,
    ( ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_24
  <=> ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f151,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f145,f138,f46,f149])).

fof(f46,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f138,plain,
    ( spl3_22
  <=> ! [X3] : r1_xboole_0(k4_xboole_0(X3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f145,plain,
    ( ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(resolution,[],[f139,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f139,plain,
    ( ! [X3] : r1_xboole_0(k4_xboole_0(X3,sK1),sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl3_22
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f136,f125,f112,f85,f138])).

fof(f85,plain,
    ( spl3_13
  <=> k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f112,plain,
    ( spl3_17
  <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f125,plain,
    ( spl3_20
  <=> ! [X9,X8,X10] : r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f136,plain,
    ( ! [X3] : r1_xboole_0(k4_xboole_0(X3,sK1),sK0)
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f130,f113])).

fof(f113,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f130,plain,
    ( ! [X3] : r1_xboole_0(k4_xboole_0(X3,k2_xboole_0(sK1,k1_xboole_0)),sK0)
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(superposition,[],[f126,f87])).

fof(f87,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f126,plain,
    ( ! [X10,X8,X9] : r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f96,f54,f38,f125])).

fof(f38,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( ! [X10,X8,X9] : r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f39,f55])).

fof(f55,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f39,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f115,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f93,f54,f34,f112])).

fof(f34,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f93,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f35,f55])).

fof(f35,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f88,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f83,f77,f42,f85])).

fof(f42,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f77,plain,
    ( spl3_12
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f83,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f43,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f43,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f80,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f75,f50,f29,f77])).

fof(f29,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f75,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f56,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f52,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f48,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f44,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f36,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f24])).

fof(f16,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (32524)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (32519)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (32524)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f165,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f27,f32,f36,f40,f44,f48,f52,f56,f80,f88,f115,f127,f140,f151,f160])).
% 0.21/0.42  fof(f160,plain,(
% 0.21/0.42    spl3_1 | ~spl3_24),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.42  fof(f156,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_24)),
% 0.21/0.42    inference(resolution,[],[f150,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) ) | ~spl3_24),
% 0.21/0.42    inference(avatar_component_clause,[],[f149])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    spl3_24 <=> ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.42  fof(f151,plain,(
% 0.21/0.42    spl3_24 | ~spl3_6 | ~spl3_22),
% 0.21/0.42    inference(avatar_split_clause,[],[f145,f138,f46,f149])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl3_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    spl3_22 <=> ! [X3] : r1_xboole_0(k4_xboole_0(X3,sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) ) | (~spl3_6 | ~spl3_22)),
% 0.21/0.42    inference(resolution,[],[f139,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f139,plain,(
% 0.21/0.42    ( ! [X3] : (r1_xboole_0(k4_xboole_0(X3,sK1),sK0)) ) | ~spl3_22),
% 0.21/0.42    inference(avatar_component_clause,[],[f138])).
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    spl3_22 | ~spl3_13 | ~spl3_17 | ~spl3_20),
% 0.21/0.42    inference(avatar_split_clause,[],[f136,f125,f112,f85,f138])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl3_13 <=> k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    spl3_17 <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    spl3_20 <=> ! [X9,X8,X10] : r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.42  fof(f136,plain,(
% 0.21/0.42    ( ! [X3] : (r1_xboole_0(k4_xboole_0(X3,sK1),sK0)) ) | (~spl3_13 | ~spl3_17 | ~spl3_20)),
% 0.21/0.42    inference(forward_demodulation,[],[f130,f113])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) ) | ~spl3_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f112])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    ( ! [X3] : (r1_xboole_0(k4_xboole_0(X3,k2_xboole_0(sK1,k1_xboole_0)),sK0)) ) | (~spl3_13 | ~spl3_20)),
% 0.21/0.42    inference(superposition,[],[f126,f87])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f85])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    ( ! [X10,X8,X9] : (r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10)) ) | ~spl3_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f125])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    spl3_20 | ~spl3_4 | ~spl3_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f96,f54,f38,f125])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl3_4 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl3_8 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    ( ! [X10,X8,X9] : (r1_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10)) ) | (~spl3_4 | ~spl3_8)),
% 0.21/0.42    inference(superposition,[],[f39,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f54])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    spl3_17 | ~spl3_3 | ~spl3_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f93,f54,f34,f112])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) ) | (~spl3_3 | ~spl3_8)),
% 0.21/0.42    inference(superposition,[],[f35,f55])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl3_13 | ~spl3_5 | ~spl3_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f83,f77,f42,f85])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl3_12 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) | (~spl3_5 | ~spl3_12)),
% 0.21/0.42    inference(superposition,[],[f43,f79])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f77])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl3_12 | ~spl3_2 | ~spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f75,f50,f29,f77])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl3_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_7)),
% 0.21/0.42    inference(resolution,[],[f51,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f29])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl3_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.42    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl3_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f42])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f38])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f29])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f24])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (32524)------------------------------
% 0.21/0.43  % (32524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (32524)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (32524)Memory used [KB]: 6140
% 0.21/0.43  % (32524)Time elapsed: 0.008 s
% 0.21/0.43  % (32524)------------------------------
% 0.21/0.43  % (32524)------------------------------
% 0.21/0.43  % (32508)Success in time 0.069 s
%------------------------------------------------------------------------------

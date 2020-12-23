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
% DateTime   : Thu Dec  3 12:48:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 189 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f36,f40,f44,f50,f55,f61,f67])).

fof(f67,plain,
    ( ~ spl2_4
    | ~ spl2_7
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_7
    | spl2_9 ),
    inference(subsumption_resolution,[],[f63,f49])).

fof(f49,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_7
  <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f63,plain,
    ( sK0 != k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_4
    | spl2_9 ),
    inference(superposition,[],[f60,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f60,plain,
    ( sK0 != k3_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_9
  <=> sK0 = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f61,plain,
    ( ~ spl2_9
    | spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f56,f53,f19,f58])).

fof(f19,plain,
    ( spl2_1
  <=> sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f53,plain,
    ( spl2_8
  <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f56,plain,
    ( sK0 != k3_xboole_0(k2_relat_1(sK1),sK0)
    | spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f21,f54])).

fof(f54,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f21,plain,
    ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f55,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f51,f38,f29,f53])).

fof(f29,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f38,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f51,plain,
    ( ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f50,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f45,f42,f24,f47])).

fof(f24,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f42,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f45,plain,
    ( sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f36,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f12,f29])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

fof(f27,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f19])).

fof(f14,plain,(
    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (680)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (680)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f22,f27,f32,f36,f40,f44,f50,f55,f61,f67])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ~spl2_4 | ~spl2_7 | spl2_9),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f66])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    $false | (~spl2_4 | ~spl2_7 | spl2_9)),
% 0.21/0.42    inference(subsumption_resolution,[],[f63,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl2_7 <=> sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    sK0 != k3_xboole_0(sK0,k2_relat_1(sK1)) | (~spl2_4 | spl2_9)),
% 0.21/0.42    inference(superposition,[],[f60,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl2_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    sK0 != k3_xboole_0(k2_relat_1(sK1),sK0) | spl2_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_9 <=> sK0 = k3_xboole_0(k2_relat_1(sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ~spl2_9 | spl2_1 | ~spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f56,f53,f19,f58])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    spl2_1 <=> sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl2_8 <=> ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    sK0 != k3_xboole_0(k2_relat_1(sK1),sK0) | (spl2_1 | ~spl2_8)),
% 0.21/0.42    inference(superposition,[],[f21,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f19])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl2_8 | ~spl2_3 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f51,f38,f29,f53])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_5 <=> ! [X1,X0] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)) ) | (~spl2_3 | ~spl2_5)),
% 0.21/0.42    inference(resolution,[],[f39,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f29])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl2_7 | ~spl2_2 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f45,f42,f24,f47])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl2_2 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) | (~spl2_2 | ~spl2_6)),
% 0.21/0.42    inference(resolution,[],[f43,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f38])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f34])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f29])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f24])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f19])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    sK0 != k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (680)------------------------------
% 0.21/0.42  % (680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (680)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (680)Memory used [KB]: 10490
% 0.21/0.42  % (680)Time elapsed: 0.005 s
% 0.21/0.42  % (680)------------------------------
% 0.21/0.42  % (680)------------------------------
% 0.21/0.42  % (674)Success in time 0.062 s
%------------------------------------------------------------------------------

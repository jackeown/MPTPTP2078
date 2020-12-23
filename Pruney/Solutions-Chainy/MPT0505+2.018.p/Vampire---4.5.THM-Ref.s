%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  87 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  135 ( 226 expanded)
%              Number of equality atoms :   37 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f41,f45,f50,f57,f63,f66])).

fof(f66,plain,
    ( ~ spl3_2
    | spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl3_2
    | spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f64,f56])).

fof(f56,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_8
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f64,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f62,f27])).

fof(f27,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f63,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f59,f48,f43,f30,f61])).

fof(f30,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f43,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f48,plain,
    ( spl3_7
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f58,f49])).

fof(f49,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X1) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f44,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f57,plain,
    ( ~ spl3_8
    | spl3_1
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f52,f48,f35,f20,f54])).

fof(f20,plain,
    ( spl3_1
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f52,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f51,f36])).

fof(f36,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f51,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0))
    | spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f22,f49])).

fof(f22,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f50,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f46,f39,f30,f48])).

fof(f39,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f46,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f41,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f30])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f20])).

fof(f15,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (19362)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (19362)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f41,f45,f50,f57,f63,f66])).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    ~spl3_2 | spl3_8 | ~spl3_9),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    $false | (~spl3_2 | spl3_8 | ~spl3_9)),
% 0.21/0.41    inference(subsumption_resolution,[],[f64,f56])).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | spl3_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f54])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    spl3_8 <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_9)),
% 0.21/0.41    inference(resolution,[],[f62,f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl3_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f61])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    spl3_9 <=> ! [X1,X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    spl3_9 | ~spl3_3 | ~spl3_6 | ~spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f59,f48,f43,f30,f61])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl3_6 <=> ! [X1,X0,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl3_7 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) ) | (~spl3_3 | ~spl3_6 | ~spl3_7)),
% 0.21/0.41    inference(forward_demodulation,[],[f58,f49])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f48])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X1)) ) | (~spl3_3 | ~spl3_6)),
% 0.21/0.41    inference(resolution,[],[f44,f32])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f30])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) ) | ~spl3_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f43])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    ~spl3_8 | spl3_1 | ~spl3_4 | ~spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f52,f48,f35,f20,f54])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    spl3_1 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_4 | ~spl3_7)),
% 0.21/0.41    inference(forward_demodulation,[],[f51,f36])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f35])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0)) | (spl3_1 | ~spl3_7)),
% 0.21/0.41    inference(superposition,[],[f22,f49])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f20])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl3_7 | ~spl3_3 | ~spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f46,f39,f30,f48])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    spl3_5 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | (~spl3_3 | ~spl3_5)),
% 0.21/0.41    inference(resolution,[],[f40,f32])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f39])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f43])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    spl3_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f13,f30])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    v1_relat_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f4])).
% 0.21/0.41  fof(f4,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f14,f25])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    r1_tarski(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ~spl3_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f15,f20])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (19362)------------------------------
% 0.21/0.41  % (19362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (19362)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (19362)Memory used [KB]: 10490
% 0.21/0.41  % (19362)Time elapsed: 0.006 s
% 0.21/0.41  % (19362)------------------------------
% 0.21/0.41  % (19362)------------------------------
% 0.21/0.41  % (19356)Success in time 0.055 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:01 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  64 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 139 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f31,f36,f42,f70,f75])).

fof(f75,plain,
    ( ~ spl3_2
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl3_2
    | spl3_10 ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f25,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_10 ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | ~ r1_tarski(sK0,sK1)
    | spl3_10 ),
    inference(superposition,[],[f69,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f69,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_10
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f70,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f60,f40,f18,f67])).

fof(f18,plain,
    ( spl3_1
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f60,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f20,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f20,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f42,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f38,f34,f28,f40])).

fof(f28,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f34,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f38,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f37,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f37,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)
    | ~ spl3_3 ),
    inference(resolution,[],[f16,f30])).

fof(f30,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f36,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f28,f34])).

fof(f32,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(resolution,[],[f15,f30])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f31,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f11,f28])).

% (31798)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f26,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f18])).

fof(f13,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (31802)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.13/0.42  % (31797)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.13/0.42  % (31797)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f76,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f21,f26,f31,f36,f42,f70,f75])).
% 0.13/0.42  fof(f75,plain,(
% 0.13/0.42    ~spl3_2 | spl3_10),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f74])).
% 0.13/0.42  fof(f74,plain,(
% 0.13/0.42    $false | (~spl3_2 | spl3_10)),
% 0.13/0.42    inference(subsumption_resolution,[],[f73,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ~r1_tarski(sK0,sK1) | spl3_10),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f72])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | ~r1_tarski(sK0,sK1) | spl3_10),
% 0.21/0.42    inference(superposition,[],[f69,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) | spl3_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f67])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    spl3_10 <=> k2_wellord1(sK2,sK0) = k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ~spl3_10 | spl3_1 | ~spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f60,f40,f18,f67])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    spl3_1 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl3_5 <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_5)),
% 0.21/0.42    inference(superposition,[],[f20,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))) ) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f18])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl3_5 | ~spl3_3 | ~spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f38,f34,f28,f40])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl3_4 <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))) ) | (~spl3_3 | ~spl3_4)),
% 0.21/0.42    inference(forward_demodulation,[],[f37,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))) ) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) ) | ~spl3_3),
% 0.21/0.42    inference(resolution,[],[f16,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl3_4 | ~spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f32,f28,f34])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.21/0.42    inference(resolution,[],[f15,f30])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f11,f28])).
% 0.21/0.42  % (31798)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f23])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f18])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (31797)------------------------------
% 0.21/0.42  % (31797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (31797)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (31797)Memory used [KB]: 10618
% 0.21/0.42  % (31797)Time elapsed: 0.006 s
% 0.21/0.42  % (31797)------------------------------
% 0.21/0.42  % (31797)------------------------------
% 0.21/0.43  % (31793)Success in time 0.072 s
%------------------------------------------------------------------------------

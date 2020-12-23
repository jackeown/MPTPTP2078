%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   95 ( 132 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f37,f44,f54,f57])).

fof(f57,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f21,plain,
    ( sK0 != k7_relat_1(sK0,k1_relat_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_1
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f55,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | sK0 = k7_relat_1(sK0,X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl1_4
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | sK0 = k7_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f53,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_7
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f54,plain,
    ( spl1_7
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f49,f42,f51])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f49,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(superposition,[],[f43,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f43,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,
    ( spl1_5
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f40,f30,f24,f42])).

fof(f24,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f30,plain,
    ( spl1_3
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f40,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f38,f26])).

fof(f26,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f38,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl1_3 ),
    inference(superposition,[],[f15,f31])).

fof(f31,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f37,plain,
    ( spl1_4
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f33,f24,f35])).

fof(f33,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | sK0 = k7_relat_1(sK0,X0) )
    | ~ spl1_2 ),
    inference(resolution,[],[f17,f26])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f32,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f24,f30])).

fof(f28,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)
    | ~ spl1_2 ),
    inference(resolution,[],[f16,f26])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f27,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f22,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    sK0 != k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (11263)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (11263)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f22,f27,f32,f37,f44,f54,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl1_1 | ~spl1_4 | ~spl1_7),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    $false | (spl1_1 | ~spl1_4 | ~spl1_7)),
% 0.20/0.43    inference(subsumption_resolution,[],[f55,f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    sK0 != k7_relat_1(sK0,k1_relat_1(sK0)) | spl1_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    spl1_1 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | (~spl1_4 | ~spl1_7)),
% 0.20/0.43    inference(resolution,[],[f53,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k7_relat_1(sK0,X0)) ) | ~spl1_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl1_4 <=> ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k7_relat_1(sK0,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~spl1_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl1_7 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl1_7 | ~spl1_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f49,f42,f51])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl1_5 <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~spl1_5),
% 0.20/0.43    inference(superposition,[],[f43,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))) ) | ~spl1_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f42])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl1_5 | ~spl1_2 | ~spl1_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f40,f30,f24,f42])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    spl1_2 <=> v1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    spl1_3 <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))) ) | (~spl1_2 | ~spl1_3)),
% 0.20/0.43    inference(subsumption_resolution,[],[f38,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    v1_relat_1(sK0) | ~spl1_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f24])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | ~spl1_3),
% 0.20/0.43    inference(superposition,[],[f15,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) ) | ~spl1_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f30])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl1_4 | ~spl1_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f24,f35])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k7_relat_1(sK0,X0)) ) | ~spl1_2),
% 0.20/0.43    inference(resolution,[],[f17,f26])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl1_3 | ~spl1_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f24,f30])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) ) | ~spl1_2),
% 0.20/0.43    inference(resolution,[],[f16,f26])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    spl1_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f12,f24])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0] : (k7_relat_1(X0,k1_relat_1(X0)) != X0 & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.43    inference(negated_conjecture,[],[f5])).
% 0.20/0.43  fof(f5,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ~spl1_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f13,f19])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    sK0 != k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (11263)------------------------------
% 0.20/0.43  % (11263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (11263)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (11263)Memory used [KB]: 10490
% 0.20/0.43  % (11263)Time elapsed: 0.006 s
% 0.20/0.43  % (11263)------------------------------
% 0.20/0.43  % (11263)------------------------------
% 0.20/0.43  % (11261)Success in time 0.075 s
%------------------------------------------------------------------------------

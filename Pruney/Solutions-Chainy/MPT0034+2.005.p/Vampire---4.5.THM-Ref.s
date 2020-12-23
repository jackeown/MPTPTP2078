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
% DateTime   : Thu Dec  3 12:29:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 112 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  142 ( 224 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f60,f65,f70,f84,f119,f124,f141,f162,f198])).

fof(f198,plain,
    ( ~ spl4_14
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f192,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f192,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(superposition,[],[f160,f118])).

fof(f118,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_14
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f160,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_19
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f162,plain,
    ( spl4_19
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f152,f63,f159])).

fof(f63,plain,
    ( spl4_7
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f152,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK1))
    | ~ spl4_7 ),
    inference(superposition,[],[f64,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f64,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f141,plain,
    ( ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f135,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f18,f19])).

fof(f135,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(superposition,[],[f82,f123])).

fof(f123,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_15
  <=> sK2 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f82,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_10
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f124,plain,
    ( spl4_15
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f109,f30,f121])).

fof(f30,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f109,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f119,plain,
    ( spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f108,f35,f116])).

fof(f35,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f108,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f84,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f74,f68,f81])).

fof(f68,plain,
    ( spl4_8
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f74,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK3))
    | ~ spl4_8 ),
    inference(superposition,[],[f69,f19])).

fof(f69,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl4_8
    | spl4_6 ),
    inference(avatar_split_clause,[],[f66,f57,f68])).

fof(f57,plain,
    ( spl4_6
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f66,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X0))
    | spl4_6 ),
    inference(resolution,[],[f59,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f59,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f65,plain,
    ( spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f61,f53,f63])).

fof(f53,plain,
    ( spl4_5
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f61,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | spl4_5 ),
    inference(resolution,[],[f55,f22])).

fof(f55,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f48,f25,f57,f53])).

fof(f25,plain,
    ( spl4_1
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl4_1 ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f38,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f33,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (697)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.41  % (694)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (689)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (689)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f199,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f60,f65,f70,f84,f119,f124,f141,f162,f198])).
% 0.21/0.42  fof(f198,plain,(
% 0.21/0.42    ~spl4_14 | ~spl4_19),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.42  fof(f197,plain,(
% 0.21/0.42    $false | (~spl4_14 | ~spl4_19)),
% 0.21/0.42    inference(subsumption_resolution,[],[f192,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.42  fof(f192,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK0) | (~spl4_14 | ~spl4_19)),
% 0.21/0.42    inference(superposition,[],[f160,f118])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f116])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl4_14 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f160,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))) ) | ~spl4_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f159])).
% 0.21/0.42  fof(f159,plain,(
% 0.21/0.42    spl4_19 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.42  fof(f162,plain,(
% 0.21/0.42    spl4_19 | ~spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f152,f63,f159])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl4_7 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK1))) ) | ~spl4_7),
% 0.21/0.42    inference(superposition,[],[f64,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f63])).
% 0.21/0.42  fof(f141,plain,(
% 0.21/0.42    ~spl4_10 | ~spl4_15),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    $false | (~spl4_10 | ~spl4_15)),
% 0.21/0.42    inference(subsumption_resolution,[],[f135,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.21/0.42    inference(superposition,[],[f18,f19])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK2) | (~spl4_10 | ~spl4_15)),
% 0.21/0.42    inference(superposition,[],[f82,f123])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    sK2 = k3_xboole_0(sK2,sK3) | ~spl4_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f121])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    spl4_15 <=> sK2 = k3_xboole_0(sK2,sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3))) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f81])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl4_10 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    spl4_15 | ~spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f109,f30,f121])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    sK2 = k3_xboole_0(sK2,sK3) | ~spl4_2),
% 0.21/0.42    inference(resolution,[],[f42,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.42    inference(superposition,[],[f20,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl4_14 | ~spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f108,f35,f116])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_3),
% 0.21/0.42    inference(resolution,[],[f42,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl4_10 | ~spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f74,f68,f81])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_8 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK3))) ) | ~spl4_8),
% 0.21/0.42    inference(superposition,[],[f69,f19])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X0))) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_8 | spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f66,f57,f68])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl4_6 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X0))) ) | spl4_6),
% 0.21/0.42    inference(resolution,[],[f59,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3) | spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    spl4_7 | spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f61,f53,f63])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl4_5 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | spl4_5),
% 0.21/0.42    inference(resolution,[],[f55,f22])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ~spl4_5 | ~spl4_6 | spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f48,f25,f57,f53])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl4_1 <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl4_1),
% 0.21/0.42    inference(resolution,[],[f23,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f35])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    r1_tarski(sK2,sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f25])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (689)------------------------------
% 0.21/0.42  % (689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (689)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (689)Memory used [KB]: 10618
% 0.21/0.42  % (689)Time elapsed: 0.009 s
% 0.21/0.42  % (689)------------------------------
% 0.21/0.42  % (689)------------------------------
% 0.21/0.43  % (687)Success in time 0.071 s
%------------------------------------------------------------------------------

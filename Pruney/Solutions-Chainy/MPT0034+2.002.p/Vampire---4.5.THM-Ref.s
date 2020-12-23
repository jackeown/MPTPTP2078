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
% DateTime   : Thu Dec  3 12:29:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 118 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  146 ( 232 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f739,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f69,f102,f107,f129,f133,f172,f245,f664,f738])).

fof(f738,plain,
    ( ~ spl4_7
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f737])).

fof(f737,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f728,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f728,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | ~ spl4_7
    | ~ spl4_24 ),
    inference(superposition,[],[f243,f106])).

fof(f106,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_7
  <=> sK2 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f243,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_24
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f664,plain,
    ( ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f654,f21])).

fof(f654,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(superposition,[],[f170,f101])).

fof(f101,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_6
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f170,plain,
    ( ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl4_15
  <=> ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f245,plain,
    ( spl4_24
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f234,f131,f242])).

fof(f131,plain,
    ( spl4_11
  <=> ! [X2] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f234,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK3))
    | ~ spl4_11 ),
    inference(superposition,[],[f132,f22])).

fof(f132,plain,
    ( ! [X2] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f172,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f161,f127,f169])).

fof(f127,plain,
    ( spl4_10
  <=> ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f161,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK1))
    | ~ spl4_10 ),
    inference(superposition,[],[f128,f22])).

fof(f128,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f133,plain,
    ( spl4_11
    | spl4_5 ),
    inference(avatar_split_clause,[],[f120,f66,f131])).

fof(f66,plain,
    ( spl4_5
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f120,plain,
    ( ! [X2] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X2))
    | spl4_5 ),
    inference(resolution,[],[f55,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r1_tarski(X2,k3_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f129,plain,
    ( spl4_10
    | spl4_4 ),
    inference(avatar_split_clause,[],[f119,f62,f127])).

fof(f62,plain,
    ( spl4_4
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X1))
    | spl4_4 ),
    inference(resolution,[],[f55,f64])).

fof(f64,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f107,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f97,f34,f104])).

fof(f34,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f97,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(superposition,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f102,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f96,f39,f99])).

fof(f39,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f96,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f69,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f57,f29,f66,f62])).

fof(f29,plain,
    ( spl4_1
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl4_1 ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f42,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f37,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:20:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.40  % (25759)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (25760)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (25753)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (25762)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (25756)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.44  % (25753)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f739,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f32,f37,f42,f69,f102,f107,f129,f133,f172,f245,f664,f738])).
% 0.20/0.44  fof(f738,plain,(
% 0.20/0.44    ~spl4_7 | ~spl4_24),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f737])).
% 0.20/0.44  fof(f737,plain,(
% 0.20/0.44    $false | (~spl4_7 | ~spl4_24)),
% 0.20/0.44    inference(subsumption_resolution,[],[f728,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.44    inference(superposition,[],[f21,f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.44  fof(f728,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK2) | (~spl4_7 | ~spl4_24)),
% 0.20/0.44    inference(superposition,[],[f243,f106])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    sK2 = k3_xboole_0(sK2,sK3) | ~spl4_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f104])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    spl4_7 <=> sK2 = k3_xboole_0(sK2,sK3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.44  fof(f243,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3))) ) | ~spl4_24),
% 0.20/0.44    inference(avatar_component_clause,[],[f242])).
% 0.20/0.44  fof(f242,plain,(
% 0.20/0.44    spl4_24 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK3))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.44  fof(f664,plain,(
% 0.20/0.44    ~spl4_6 | ~spl4_15),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f663])).
% 0.20/0.44  fof(f663,plain,(
% 0.20/0.44    $false | (~spl4_6 | ~spl4_15)),
% 0.20/0.44    inference(subsumption_resolution,[],[f654,f21])).
% 0.20/0.44  fof(f654,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK0) | (~spl4_6 | ~spl4_15)),
% 0.20/0.44    inference(superposition,[],[f170,f101])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f99])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    spl4_6 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.44  fof(f170,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))) ) | ~spl4_15),
% 0.20/0.44    inference(avatar_component_clause,[],[f169])).
% 0.20/0.44  fof(f169,plain,(
% 0.20/0.44    spl4_15 <=> ! [X0] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.44  fof(f245,plain,(
% 0.20/0.44    spl4_24 | ~spl4_11),
% 0.20/0.44    inference(avatar_split_clause,[],[f234,f131,f242])).
% 0.20/0.44  fof(f131,plain,(
% 0.20/0.44    spl4_11 <=> ! [X2] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.44  fof(f234,plain,(
% 0.20/0.44    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK3))) ) | ~spl4_11),
% 0.20/0.44    inference(superposition,[],[f132,f22])).
% 0.20/0.44  fof(f132,plain,(
% 0.20/0.44    ( ! [X2] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X2))) ) | ~spl4_11),
% 0.20/0.44    inference(avatar_component_clause,[],[f131])).
% 0.20/0.44  fof(f172,plain,(
% 0.20/0.44    spl4_15 | ~spl4_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f161,f127,f169])).
% 0.20/0.44  fof(f127,plain,(
% 0.20/0.44    spl4_10 <=> ! [X1] : ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.44  fof(f161,plain,(
% 0.20/0.44    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X1,sK1))) ) | ~spl4_10),
% 0.20/0.44    inference(superposition,[],[f128,f22])).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X1))) ) | ~spl4_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f127])).
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    spl4_11 | spl4_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f120,f66,f131])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    spl4_5 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    ( ! [X2] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK3,X2))) ) | spl4_5),
% 0.20/0.44    inference(resolution,[],[f55,f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3) | spl4_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f66])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r1_tarski(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(superposition,[],[f26,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    spl4_10 | spl4_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f119,f62,f127])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    spl4_4 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.44  fof(f119,plain,(
% 0.20/0.44    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X1))) ) | spl4_4),
% 0.20/0.44    inference(resolution,[],[f55,f64])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl4_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f62])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    spl4_7 | ~spl4_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f97,f34,f104])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    sK2 = k3_xboole_0(sK2,sK3) | ~spl4_2),
% 0.20/0.44    inference(resolution,[],[f52,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f34])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.44    inference(superposition,[],[f24,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    spl4_6 | ~spl4_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f96,f39,f99])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.44  fof(f96,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_3),
% 0.20/0.44    inference(resolution,[],[f52,f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f39])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    ~spl4_4 | ~spl4_5 | spl4_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f57,f29,f66,f62])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    spl4_1 <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl4_1),
% 0.20/0.44    inference(resolution,[],[f27,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) | spl4_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f29])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    spl4_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f17,f39])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.20/0.44    inference(flattening,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.20/0.44    inference(negated_conjecture,[],[f9])).
% 0.20/0.44  fof(f9,conjecture,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    spl4_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f18,f34])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    r1_tarski(sK2,sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ~spl4_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f19,f29])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (25753)------------------------------
% 0.20/0.44  % (25753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (25753)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (25753)Memory used [KB]: 11001
% 0.20/0.44  % (25753)Time elapsed: 0.021 s
% 0.20/0.44  % (25753)------------------------------
% 0.20/0.44  % (25753)------------------------------
% 0.20/0.44  % (25751)Success in time 0.091 s
%------------------------------------------------------------------------------

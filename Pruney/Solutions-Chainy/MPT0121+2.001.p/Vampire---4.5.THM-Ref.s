%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 108 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  147 ( 243 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f53,f70,f161,f174,f182,f250,f457])).

fof(f457,plain,
    ( spl4_7
    | ~ spl4_23
    | ~ spl4_25
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | spl4_7
    | ~ spl4_23
    | ~ spl4_25
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f455,f248])).

fof(f248,plain,
    ( ! [X1] : r1_xboole_0(k3_xboole_0(X1,sK1),sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl4_36
  <=> ! [X1] : r1_xboole_0(k3_xboole_0(X1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f455,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,sK1),sK3)
    | spl4_7
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f439,f181])).

fof(f181,plain,
    ( ! [X2] : k3_xboole_0(sK3,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK3,X2)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_25
  <=> ! [X2] : k3_xboole_0(sK3,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f439,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)),sK3)
    | spl4_7
    | ~ spl4_23 ),
    inference(superposition,[],[f69,f173])).

fof(f173,plain,
    ( ! [X0] : k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_23
  <=> ! [X0] : k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f69,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_7
  <=> r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f250,plain,
    ( spl4_36
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f233,f159,f247])).

fof(f159,plain,
    ( spl4_21
  <=> ! [X1] : r1_xboole_0(k3_xboole_0(sK1,X1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f233,plain,
    ( ! [X2] : r1_xboole_0(k3_xboole_0(X2,sK1),sK3)
    | ~ spl4_21 ),
    inference(superposition,[],[f160,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f160,plain,
    ( ! [X1] : r1_xboole_0(k3_xboole_0(sK1,X1),sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f182,plain,
    ( spl4_25
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f168,f44,f180])).

fof(f44,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f168,plain,
    ( ! [X2] : k3_xboole_0(sK3,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK3,X2)
    | ~ spl4_4 ),
    inference(resolution,[],[f81,f46])).

fof(f46,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f81,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(X7,X6)
      | k3_xboole_0(X6,k2_xboole_0(X7,X8)) = k3_xboole_0(X6,X8) ) ),
    inference(resolution,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f174,plain,
    ( spl4_23
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f166,f34,f172])).

fof(f34,plain,
    ( spl4_2
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f166,plain,
    ( ! [X0] : k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0)
    | ~ spl4_2 ),
    inference(resolution,[],[f81,f36])).

fof(f36,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f161,plain,
    ( spl4_21
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f150,f39,f159])).

fof(f39,plain,
    ( spl4_3
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f150,plain,
    ( ! [X1] : r1_xboole_0(k3_xboole_0(sK1,X1),sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k3_xboole_0(X0,X2),X1) ) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f70,plain,
    ( ~ spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f65,f50,f67])).

fof(f50,plain,
    ( spl4_5
  <=> r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f65,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),sK3)
    | spl4_5 ),
    inference(forward_demodulation,[],[f63,f23])).

fof(f63,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3),sK3)
    | spl4_5 ),
    inference(resolution,[],[f25,f52])).

fof(f52,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f53,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f48,f29,f50])).

fof(f29,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)
    | spl4_1 ),
    inference(forward_demodulation,[],[f31,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f31,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f47,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f42,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f20,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:13:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (8808)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (8812)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % (8809)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (8814)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.44  % (8805)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.45  % (8815)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.45  % (8805)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f466,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f53,f70,f161,f174,f182,f250,f457])).
% 0.22/0.45  fof(f457,plain,(
% 0.22/0.45    spl4_7 | ~spl4_23 | ~spl4_25 | ~spl4_36),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f456])).
% 0.22/0.45  fof(f456,plain,(
% 0.22/0.45    $false | (spl4_7 | ~spl4_23 | ~spl4_25 | ~spl4_36)),
% 0.22/0.45    inference(subsumption_resolution,[],[f455,f248])).
% 0.22/0.45  fof(f248,plain,(
% 0.22/0.45    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,sK1),sK3)) ) | ~spl4_36),
% 0.22/0.45    inference(avatar_component_clause,[],[f247])).
% 0.22/0.45  fof(f247,plain,(
% 0.22/0.45    spl4_36 <=> ! [X1] : r1_xboole_0(k3_xboole_0(X1,sK1),sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.45  fof(f455,plain,(
% 0.22/0.45    ~r1_xboole_0(k3_xboole_0(sK3,sK1),sK3) | (spl4_7 | ~spl4_23 | ~spl4_25)),
% 0.22/0.45    inference(forward_demodulation,[],[f439,f181])).
% 0.22/0.45  fof(f181,plain,(
% 0.22/0.45    ( ! [X2] : (k3_xboole_0(sK3,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK3,X2)) ) | ~spl4_25),
% 0.22/0.45    inference(avatar_component_clause,[],[f180])).
% 0.22/0.45  fof(f180,plain,(
% 0.22/0.45    spl4_25 <=> ! [X2] : k3_xboole_0(sK3,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK3,X2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.45  fof(f439,plain,(
% 0.22/0.45    ~r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)),sK3) | (spl4_7 | ~spl4_23)),
% 0.22/0.45    inference(superposition,[],[f69,f173])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    ( ! [X0] : (k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0)) ) | ~spl4_23),
% 0.22/0.45    inference(avatar_component_clause,[],[f172])).
% 0.22/0.45  fof(f172,plain,(
% 0.22/0.45    spl4_23 <=> ! [X0] : k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ~r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),sK3) | spl4_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    spl4_7 <=> r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.45  fof(f250,plain,(
% 0.22/0.45    spl4_36 | ~spl4_21),
% 0.22/0.45    inference(avatar_split_clause,[],[f233,f159,f247])).
% 0.22/0.45  fof(f159,plain,(
% 0.22/0.45    spl4_21 <=> ! [X1] : r1_xboole_0(k3_xboole_0(sK1,X1),sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.45  fof(f233,plain,(
% 0.22/0.45    ( ! [X2] : (r1_xboole_0(k3_xboole_0(X2,sK1),sK3)) ) | ~spl4_21),
% 0.22/0.45    inference(superposition,[],[f160,f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.45  fof(f160,plain,(
% 0.22/0.45    ( ! [X1] : (r1_xboole_0(k3_xboole_0(sK1,X1),sK3)) ) | ~spl4_21),
% 0.22/0.45    inference(avatar_component_clause,[],[f159])).
% 0.22/0.45  fof(f182,plain,(
% 0.22/0.45    spl4_25 | ~spl4_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f168,f44,f180])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl4_4 <=> r1_xboole_0(sK0,sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.45  fof(f168,plain,(
% 0.22/0.45    ( ! [X2] : (k3_xboole_0(sK3,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK3,X2)) ) | ~spl4_4),
% 0.22/0.45    inference(resolution,[],[f81,f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    r1_xboole_0(sK0,sK3) | ~spl4_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    ( ! [X6,X8,X7] : (~r1_xboole_0(X7,X6) | k3_xboole_0(X6,k2_xboole_0(X7,X8)) = k3_xboole_0(X6,X8)) )),
% 0.22/0.45    inference(resolution,[],[f26,f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    spl4_23 | ~spl4_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f166,f34,f172])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    spl4_2 <=> r1_xboole_0(sK2,sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.45  fof(f166,plain,(
% 0.22/0.45    ( ! [X0] : (k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0)) ) | ~spl4_2),
% 0.22/0.45    inference(resolution,[],[f81,f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    r1_xboole_0(sK2,sK3) | ~spl4_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f34])).
% 0.22/0.45  fof(f161,plain,(
% 0.22/0.45    spl4_21 | ~spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f150,f39,f159])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    spl4_3 <=> r1_xboole_0(sK1,sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.45  fof(f150,plain,(
% 0.22/0.45    ( ! [X1] : (r1_xboole_0(k3_xboole_0(sK1,X1),sK3)) ) | ~spl4_3),
% 0.22/0.45    inference(resolution,[],[f76,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    r1_xboole_0(sK1,sK3) | ~spl4_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f39])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X2),X1)) )),
% 0.22/0.45    inference(resolution,[],[f27,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    ~spl4_7 | spl4_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f65,f50,f67])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl4_5 <=> r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    ~r1_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),sK3) | spl4_5),
% 0.22/0.45    inference(forward_demodulation,[],[f63,f23])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ~r1_xboole_0(k3_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3),sK3) | spl4_5),
% 0.22/0.45    inference(resolution,[],[f25,f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ~r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) | spl4_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f50])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ~spl4_5 | spl4_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f48,f29,f50])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    spl4_1 <=> r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ~r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) | spl4_1),
% 0.22/0.45    inference(forward_demodulation,[],[f31,f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) | spl4_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f29])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl4_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f17,f44])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    r1_xboole_0(sK0,sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f18,f39])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    r1_xboole_0(sK1,sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    spl4_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f19,f34])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    r1_xboole_0(sK2,sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ~spl4_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f29])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (8805)------------------------------
% 0.22/0.45  % (8805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (8805)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (8805)Memory used [KB]: 10874
% 0.22/0.45  % (8805)Time elapsed: 0.042 s
% 0.22/0.45  % (8805)------------------------------
% 0.22/0.45  % (8805)------------------------------
% 0.22/0.46  % (8803)Success in time 0.095 s
%------------------------------------------------------------------------------

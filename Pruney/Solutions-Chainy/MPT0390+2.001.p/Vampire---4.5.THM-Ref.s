%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   87 ( 129 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f46,f81,f123,f171])).

fof(f171,plain,
    ( spl3_1
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_1
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f157,f22])).

fof(f22,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> r1_tarski(k1_setfam_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f157,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2)
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(superposition,[],[f121,f45])).

fof(f45,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_5
  <=> sK2 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f121,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(sK0,X0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_17
  <=> ! [X0] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f123,plain,
    ( spl3_17
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f109,f79,f120])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X0] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(X0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f109,plain,
    ( ! [X1] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(sK0,X1))
    | ~ spl3_11 ),
    inference(superposition,[],[f80,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f80,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(X0,sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f77,f30,f79])).

fof(f30,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(X0,sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f48,f32])).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f48,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r1_tarski(k1_setfam_1(X1),k2_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f46,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f40,f25,f43])).

fof(f25,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f17,f27])).

fof(f27,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f20])).

fof(f14,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (20718)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.41  % (20716)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.42  % (20710)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.19/0.42  % (20714)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.42  % (20715)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (20710)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f176,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f23,f28,f33,f46,f81,f123,f171])).
% 0.19/0.42  fof(f171,plain,(
% 0.19/0.42    spl3_1 | ~spl3_5 | ~spl3_17),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f170])).
% 0.19/0.42  fof(f170,plain,(
% 0.19/0.42    $false | (spl3_1 | ~spl3_5 | ~spl3_17)),
% 0.19/0.42    inference(subsumption_resolution,[],[f157,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ~r1_tarski(k1_setfam_1(sK1),sK2) | spl3_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    spl3_1 <=> r1_tarski(k1_setfam_1(sK1),sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.42  fof(f157,plain,(
% 0.19/0.42    r1_tarski(k1_setfam_1(sK1),sK2) | (~spl3_5 | ~spl3_17)),
% 0.19/0.42    inference(superposition,[],[f121,f45])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    sK2 = k2_xboole_0(sK0,sK2) | ~spl3_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    spl3_5 <=> sK2 = k2_xboole_0(sK0,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.42  fof(f121,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k1_setfam_1(sK1),k2_xboole_0(sK0,X0))) ) | ~spl3_17),
% 0.19/0.42    inference(avatar_component_clause,[],[f120])).
% 0.19/0.42  fof(f120,plain,(
% 0.19/0.42    spl3_17 <=> ! [X0] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(sK0,X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.42  fof(f123,plain,(
% 0.19/0.42    spl3_17 | ~spl3_11),
% 0.19/0.42    inference(avatar_split_clause,[],[f109,f79,f120])).
% 0.19/0.42  fof(f79,plain,(
% 0.19/0.42    spl3_11 <=> ! [X0] : r1_tarski(k1_setfam_1(sK1),k2_xboole_0(X0,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.42  fof(f109,plain,(
% 0.19/0.42    ( ! [X1] : (r1_tarski(k1_setfam_1(sK1),k2_xboole_0(sK0,X1))) ) | ~spl3_11),
% 0.19/0.42    inference(superposition,[],[f80,f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.42  fof(f80,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k1_setfam_1(sK1),k2_xboole_0(X0,sK0))) ) | ~spl3_11),
% 0.19/0.42    inference(avatar_component_clause,[],[f79])).
% 0.19/0.42  fof(f81,plain,(
% 0.19/0.42    spl3_11 | ~spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f77,f30,f79])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    spl3_3 <=> r2_hidden(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k1_setfam_1(sK1),k2_xboole_0(X0,sK0))) ) | ~spl3_3),
% 0.19/0.42    inference(resolution,[],[f48,f32])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    r2_hidden(sK0,sK1) | ~spl3_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f30])).
% 0.19/0.43  fof(f48,plain,(
% 0.19/0.43    ( ! [X2,X3,X1] : (~r2_hidden(X3,X1) | r1_tarski(k1_setfam_1(X1),k2_xboole_0(X2,X3))) )),
% 0.19/0.43    inference(resolution,[],[f18,f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f11])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    spl3_5 | ~spl3_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f40,f25,f43])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    sK2 = k2_xboole_0(sK0,sK2) | ~spl3_2),
% 0.19/0.43    inference(resolution,[],[f17,f27])).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f25])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.43    inference(cnf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    spl3_3),
% 0.19/0.43    inference(avatar_split_clause,[],[f12,f30])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    r2_hidden(sK0,sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,plain,(
% 0.19/0.43    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1))),
% 0.19/0.43    inference(flattening,[],[f7])).
% 0.19/0.43  fof(f7,plain,(
% 0.19/0.43    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & (r1_tarski(X0,X2) & r2_hidden(X0,X1)))),
% 0.19/0.43    inference(ennf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.19/0.43    inference(negated_conjecture,[],[f5])).
% 0.19/0.43  fof(f5,conjecture,(
% 0.19/0.43    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    spl3_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f13,f25])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    r1_tarski(sK0,sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f8])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ~spl3_1),
% 0.19/0.43    inference(avatar_split_clause,[],[f14,f20])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ~r1_tarski(k1_setfam_1(sK1),sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f8])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (20710)------------------------------
% 0.19/0.43  % (20710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (20710)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (20710)Memory used [KB]: 10618
% 0.19/0.43  % (20710)Time elapsed: 0.007 s
% 0.19/0.43  % (20710)------------------------------
% 0.19/0.43  % (20710)------------------------------
% 0.20/0.43  % (20708)Success in time 0.076 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:38 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   49 (  82 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 180 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f90])).

fof(f90,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f88,f43,f38,f33])).

fof(f33,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f38,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f43,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f88,plain,
    ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f70,f79])).

fof(f79,plain,
    ( ! [X0] : k6_subset_1(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0))
    | ~ spl4_3 ),
    inference(resolution,[],[f64,f45])).

fof(f45,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k6_subset_1(X0,k7_relat_1(X0,X1)) = k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f27,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

% (12142)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f70,plain,
    ( ! [X3] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k6_subset_1(X3,sK1)),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f57,f54])).

fof(f54,plain,
    ( ! [X0] : r1_xboole_0(k6_subset_1(X0,sK1),sK0)
    | ~ spl4_2 ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,
    ( ! [X0] : sK0 = k6_subset_1(sK0,k6_subset_1(X0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f49,plain,
    ( ! [X0] : r1_xboole_0(sK0,k6_subset_1(X0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k6_subset_1(X2,X1)) ) ),
    inference(definition_unfolding,[],[f28,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f50,plain,(
    ! [X2,X1] : r1_xboole_0(X1,k6_subset_1(X2,X1)) ),
    inference(resolution,[],[f31,f48])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f26,f45])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f46,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f33])).

% (12141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f19,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:15:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (12139)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (12147)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.52  % (12147)Refutation not found, incomplete strategy% (12147)------------------------------
% 1.28/0.52  % (12147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (12147)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (12147)Memory used [KB]: 10618
% 1.28/0.53  % (12147)Time elapsed: 0.101 s
% 1.28/0.53  % (12147)------------------------------
% 1.28/0.53  % (12147)------------------------------
% 1.28/0.53  % (12139)Refutation not found, incomplete strategy% (12139)------------------------------
% 1.28/0.53  % (12139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (12139)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (12139)Memory used [KB]: 1791
% 1.28/0.53  % (12139)Time elapsed: 0.116 s
% 1.28/0.53  % (12139)------------------------------
% 1.28/0.53  % (12139)------------------------------
% 1.28/0.53  % (12164)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.53  % (12155)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.53  % (12145)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (12155)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % (12162)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f91,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(avatar_sat_refutation,[],[f36,f41,f46,f90])).
% 1.28/0.54  fof(f90,plain,(
% 1.28/0.54    spl4_1 | ~spl4_2 | ~spl4_3),
% 1.28/0.54    inference(avatar_split_clause,[],[f88,f43,f38,f33])).
% 1.28/0.54  fof(f33,plain,(
% 1.28/0.54    spl4_1 <=> k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.28/0.54  fof(f38,plain,(
% 1.28/0.54    spl4_2 <=> r1_tarski(sK0,sK1)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.28/0.54  fof(f43,plain,(
% 1.28/0.54    spl4_3 <=> v1_relat_1(sK2)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.28/0.54  fof(f88,plain,(
% 1.28/0.54    k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) | (~spl4_2 | ~spl4_3)),
% 1.28/0.54    inference(superposition,[],[f70,f79])).
% 1.28/0.54  fof(f79,plain,(
% 1.28/0.54    ( ! [X0] : (k6_subset_1(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0))) ) | ~spl4_3),
% 1.28/0.54    inference(resolution,[],[f64,f45])).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    v1_relat_1(sK2) | ~spl4_3),
% 1.28/0.54    inference(avatar_component_clause,[],[f43])).
% 1.28/0.54  fof(f64,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k6_subset_1(X0,k7_relat_1(X0,X1)) = k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) )),
% 1.28/0.54    inference(resolution,[],[f27,f48])).
% 1.28/0.54  fof(f48,plain,(
% 1.28/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f47])).
% 1.28/0.54  fof(f47,plain,(
% 1.28/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.28/0.54    inference(resolution,[],[f25,f24])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f11])).
% 1.28/0.54  fof(f11,plain,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f1])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f11])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f15])).
% 1.28/0.54  fof(f15,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.28/0.54    inference(flattening,[],[f14])).
% 1.28/0.54  fof(f14,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 1.28/0.54    inference(ennf_transformation,[],[f6])).
% 1.28/0.54  % (12142)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 1.28/0.54  fof(f70,plain,(
% 1.28/0.54    ( ! [X3] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k6_subset_1(X3,sK1)),sK0)) ) | (~spl4_2 | ~spl4_3)),
% 1.28/0.54    inference(resolution,[],[f57,f54])).
% 1.28/0.54  fof(f54,plain,(
% 1.28/0.54    ( ! [X0] : (r1_xboole_0(k6_subset_1(X0,sK1),sK0)) ) | ~spl4_2),
% 1.28/0.54    inference(superposition,[],[f50,f51])).
% 1.28/0.54  fof(f51,plain,(
% 1.28/0.54    ( ! [X0] : (sK0 = k6_subset_1(sK0,k6_subset_1(X0,sK1))) ) | ~spl4_2),
% 1.28/0.54    inference(resolution,[],[f49,f29])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 1.28/0.54    inference(definition_unfolding,[],[f22,f20])).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f2])).
% 1.28/0.54  fof(f2,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.28/0.54  fof(f49,plain,(
% 1.28/0.54    ( ! [X0] : (r1_xboole_0(sK0,k6_subset_1(X0,sK1))) ) | ~spl4_2),
% 1.28/0.54    inference(resolution,[],[f31,f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    r1_tarski(sK0,sK1) | ~spl4_2),
% 1.28/0.54    inference(avatar_component_clause,[],[f38])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k6_subset_1(X2,X1))) )),
% 1.28/0.54    inference(definition_unfolding,[],[f28,f20])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.28/0.54    inference(ennf_transformation,[],[f3])).
% 1.28/0.54  fof(f3,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.28/0.54  fof(f50,plain,(
% 1.28/0.54    ( ! [X2,X1] : (r1_xboole_0(X1,k6_subset_1(X2,X1))) )),
% 1.28/0.54    inference(resolution,[],[f31,f48])).
% 1.28/0.54  fof(f57,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl4_3),
% 1.28/0.54    inference(resolution,[],[f26,f45])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f13])).
% 1.28/0.54  fof(f13,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.28/0.54    inference(flattening,[],[f12])).
% 1.28/0.54  fof(f12,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.28/0.54    inference(ennf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    spl4_3),
% 1.28/0.54    inference(avatar_split_clause,[],[f17,f43])).
% 1.28/0.54  fof(f17,plain,(
% 1.28/0.54    v1_relat_1(sK2)),
% 1.28/0.54    inference(cnf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,plain,(
% 1.28/0.54    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.28/0.54    inference(flattening,[],[f9])).
% 1.28/0.54  fof(f9,plain,(
% 1.28/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.28/0.54    inference(ennf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,negated_conjecture,(
% 1.28/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.28/0.54    inference(negated_conjecture,[],[f7])).
% 1.28/0.54  fof(f7,conjecture,(
% 1.28/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    spl4_2),
% 1.28/0.54    inference(avatar_split_clause,[],[f18,f38])).
% 1.28/0.54  fof(f18,plain,(
% 1.28/0.54    r1_tarski(sK0,sK1)),
% 1.28/0.54    inference(cnf_transformation,[],[f10])).
% 1.28/0.54  fof(f36,plain,(
% 1.28/0.54    ~spl4_1),
% 1.28/0.54    inference(avatar_split_clause,[],[f19,f33])).
% 1.28/0.54  % (12141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  fof(f19,plain,(
% 1.28/0.54    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.28/0.54    inference(cnf_transformation,[],[f10])).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (12155)------------------------------
% 1.28/0.54  % (12155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (12155)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (12155)Memory used [KB]: 10746
% 1.28/0.54  % (12155)Time elapsed: 0.126 s
% 1.28/0.54  % (12155)------------------------------
% 1.28/0.54  % (12155)------------------------------
% 1.28/0.54  % (12143)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (12144)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (12143)Refutation not found, incomplete strategy% (12143)------------------------------
% 1.28/0.54  % (12143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (12141)Refutation not found, incomplete strategy% (12141)------------------------------
% 1.39/0.54  % (12141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (12138)Success in time 0.176 s
%------------------------------------------------------------------------------

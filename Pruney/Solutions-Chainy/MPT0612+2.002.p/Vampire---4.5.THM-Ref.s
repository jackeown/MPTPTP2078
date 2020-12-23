%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:35 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   52 (  80 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 169 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f86,f1101])).

fof(f1101,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1099,f83,f77,f72,f67])).

fof(f67,plain,
    ( spl5_1
  <=> k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f72,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f77,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f83,plain,
    ( spl5_4
  <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1099,plain,
    ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f530,f392])).

fof(f392,plain,
    ( ! [X0] : k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0)) = k6_subset_1(sK2,k7_relat_1(sK2,X0))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f198,f85])).

fof(f85,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f198,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))
    | ~ spl5_3 ),
    inference(resolution,[],[f50,f79])).

fof(f79,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f530,plain,
    ( ! [X8] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k6_subset_1(X8,sK1)),sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f351,f93])).

fof(f93,plain,
    ( ! [X0] : sK0 = k6_subset_1(sK0,k6_subset_1(X0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f90,plain,
    ( ! [X0] : r1_xboole_0(sK0,k6_subset_1(X0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f61,f74])).

fof(f74,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k6_subset_1(X2,X1)) ) ),
    inference(definition_unfolding,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f351,plain,
    ( ! [X0,X1] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),k6_subset_1(X1,X0))
    | ~ spl5_3 ),
    inference(resolution,[],[f195,f92])).

fof(f92,plain,(
    ! [X4,X3] : r1_xboole_0(X3,k6_subset_1(X4,X3)) ),
    inference(resolution,[],[f61,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f51,f79])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f86,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f81,f77,f83])).

fof(f81,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f34,f79])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f75,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f67])).

fof(f32,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (29961)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (29972)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (29957)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (29964)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (29960)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (29956)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (29958)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (29985)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (29969)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.53  % (29978)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (29970)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.53  % (29967)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.53  % (29968)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (29971)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.53  % (29959)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.53  % (29978)Refutation not found, incomplete strategy% (29978)------------------------------
% 1.26/0.53  % (29978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (29978)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (29978)Memory used [KB]: 10746
% 1.26/0.53  % (29978)Time elapsed: 0.093 s
% 1.26/0.53  % (29978)------------------------------
% 1.26/0.53  % (29978)------------------------------
% 1.26/0.53  % (29974)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.26/0.53  % (29962)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.54  % (29963)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.54  % (29984)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.54  % (29982)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.26/0.54  % (29983)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.26/0.54  % (29979)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.55  % (29975)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (29976)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (29966)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.55  % (29980)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.55  % (29965)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.55  % (29967)Refutation not found, incomplete strategy% (29967)------------------------------
% 1.39/0.55  % (29967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29967)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (29967)Memory used [KB]: 10746
% 1.39/0.55  % (29967)Time elapsed: 0.135 s
% 1.39/0.55  % (29967)------------------------------
% 1.39/0.55  % (29967)------------------------------
% 1.39/0.55  % (29981)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.56  % (29977)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.56  % (29973)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.57  % (29972)Refutation found. Thanks to Tanya!
% 1.39/0.57  % SZS status Theorem for theBenchmark
% 1.39/0.58  % SZS output start Proof for theBenchmark
% 1.39/0.58  fof(f1102,plain,(
% 1.39/0.58    $false),
% 1.39/0.58    inference(avatar_sat_refutation,[],[f70,f75,f80,f86,f1101])).
% 1.39/0.58  fof(f1101,plain,(
% 1.39/0.58    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 1.39/0.58    inference(avatar_split_clause,[],[f1099,f83,f77,f72,f67])).
% 1.39/0.58  fof(f67,plain,(
% 1.39/0.58    spl5_1 <=> k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.39/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.39/0.58  fof(f72,plain,(
% 1.39/0.58    spl5_2 <=> r1_tarski(sK0,sK1)),
% 1.39/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.39/0.58  fof(f77,plain,(
% 1.39/0.58    spl5_3 <=> v1_relat_1(sK2)),
% 1.39/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.39/0.58  fof(f83,plain,(
% 1.39/0.58    spl5_4 <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 1.39/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.39/0.58  fof(f1099,plain,(
% 1.39/0.58    k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 1.39/0.58    inference(superposition,[],[f530,f392])).
% 1.39/0.58  fof(f392,plain,(
% 1.39/0.58    ( ! [X0] : (k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0)) = k6_subset_1(sK2,k7_relat_1(sK2,X0))) ) | (~spl5_3 | ~spl5_4)),
% 1.39/0.58    inference(superposition,[],[f198,f85])).
% 1.39/0.58  fof(f85,plain,(
% 1.39/0.58    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl5_4),
% 1.39/0.58    inference(avatar_component_clause,[],[f83])).
% 1.39/0.58  fof(f198,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k7_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) ) | ~spl5_3),
% 1.39/0.58    inference(resolution,[],[f50,f79])).
% 1.39/0.58  fof(f79,plain,(
% 1.39/0.58    v1_relat_1(sK2) | ~spl5_3),
% 1.39/0.58    inference(avatar_component_clause,[],[f77])).
% 1.39/0.58  fof(f50,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 1.39/0.58    inference(cnf_transformation,[],[f25])).
% 1.39/0.58  fof(f25,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.39/0.58    inference(ennf_transformation,[],[f13])).
% 1.39/0.58  fof(f13,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).
% 1.39/0.58  fof(f530,plain,(
% 1.39/0.58    ( ! [X8] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k6_subset_1(X8,sK1)),sK0)) ) | (~spl5_2 | ~spl5_3)),
% 1.39/0.58    inference(superposition,[],[f351,f93])).
% 1.39/0.58  fof(f93,plain,(
% 1.39/0.58    ( ! [X0] : (sK0 = k6_subset_1(sK0,k6_subset_1(X0,sK1))) ) | ~spl5_2),
% 1.39/0.58    inference(resolution,[],[f90,f58])).
% 1.39/0.58  fof(f58,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 1.39/0.58    inference(definition_unfolding,[],[f48,f37])).
% 1.39/0.58  fof(f37,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f11])).
% 1.39/0.58  fof(f11,axiom,(
% 1.39/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.39/0.58  fof(f48,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f8])).
% 1.39/0.58  fof(f8,axiom,(
% 1.39/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.39/0.58  fof(f90,plain,(
% 1.39/0.58    ( ! [X0] : (r1_xboole_0(sK0,k6_subset_1(X0,sK1))) ) | ~spl5_2),
% 1.39/0.58    inference(resolution,[],[f61,f74])).
% 1.39/0.58  fof(f74,plain,(
% 1.39/0.58    r1_tarski(sK0,sK1) | ~spl5_2),
% 1.39/0.58    inference(avatar_component_clause,[],[f72])).
% 1.39/0.58  fof(f61,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k6_subset_1(X2,X1))) )),
% 1.39/0.58    inference(definition_unfolding,[],[f52,f37])).
% 1.39/0.58  fof(f52,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 1.39/0.58    inference(cnf_transformation,[],[f28])).
% 1.39/0.58  fof(f28,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.39/0.58    inference(ennf_transformation,[],[f9])).
% 1.39/0.58  fof(f9,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.39/0.58  fof(f351,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),k6_subset_1(X1,X0))) ) | ~spl5_3),
% 1.39/0.58    inference(resolution,[],[f195,f92])).
% 1.39/0.58  fof(f92,plain,(
% 1.39/0.58    ( ! [X4,X3] : (r1_xboole_0(X3,k6_subset_1(X4,X3))) )),
% 1.39/0.58    inference(resolution,[],[f61,f64])).
% 1.39/0.58  fof(f64,plain,(
% 1.39/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.58    inference(equality_resolution,[],[f42])).
% 1.39/0.58  fof(f42,plain,(
% 1.39/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.58    inference(cnf_transformation,[],[f3])).
% 1.39/0.58  fof(f3,axiom,(
% 1.39/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.58  fof(f195,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl5_3),
% 1.39/0.58    inference(resolution,[],[f51,f79])).
% 1.39/0.58  fof(f51,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f27])).
% 1.39/0.58  fof(f27,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.39/0.58    inference(flattening,[],[f26])).
% 1.39/0.58  fof(f26,plain,(
% 1.39/0.58    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.39/0.58    inference(ennf_transformation,[],[f14])).
% 1.39/0.58  fof(f14,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.39/0.58  fof(f86,plain,(
% 1.39/0.58    spl5_4 | ~spl5_3),
% 1.39/0.58    inference(avatar_split_clause,[],[f81,f77,f83])).
% 1.39/0.58  fof(f81,plain,(
% 1.39/0.58    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl5_3),
% 1.39/0.58    inference(resolution,[],[f34,f79])).
% 1.39/0.58  fof(f34,plain,(
% 1.39/0.58    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.39/0.58    inference(cnf_transformation,[],[f21])).
% 1.39/0.58  fof(f21,plain,(
% 1.39/0.58    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.39/0.58    inference(ennf_transformation,[],[f15])).
% 1.39/0.58  fof(f15,axiom,(
% 1.39/0.58    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.39/0.58  fof(f80,plain,(
% 1.39/0.58    spl5_3),
% 1.39/0.58    inference(avatar_split_clause,[],[f30,f77])).
% 1.39/0.58  fof(f30,plain,(
% 1.39/0.58    v1_relat_1(sK2)),
% 1.39/0.58    inference(cnf_transformation,[],[f20])).
% 1.39/0.58  fof(f20,plain,(
% 1.39/0.58    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.39/0.58    inference(flattening,[],[f19])).
% 1.39/0.58  fof(f19,plain,(
% 1.39/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.39/0.58    inference(ennf_transformation,[],[f17])).
% 1.39/0.58  fof(f17,negated_conjecture,(
% 1.39/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.39/0.58    inference(negated_conjecture,[],[f16])).
% 1.39/0.58  fof(f16,conjecture,(
% 1.39/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 1.39/0.58  fof(f75,plain,(
% 1.39/0.58    spl5_2),
% 1.39/0.58    inference(avatar_split_clause,[],[f31,f72])).
% 1.39/0.58  fof(f31,plain,(
% 1.39/0.58    r1_tarski(sK0,sK1)),
% 1.39/0.58    inference(cnf_transformation,[],[f20])).
% 1.39/0.58  fof(f70,plain,(
% 1.39/0.58    ~spl5_1),
% 1.39/0.58    inference(avatar_split_clause,[],[f32,f67])).
% 1.39/0.58  fof(f32,plain,(
% 1.39/0.58    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 1.39/0.58    inference(cnf_transformation,[],[f20])).
% 1.39/0.58  % SZS output end Proof for theBenchmark
% 1.39/0.58  % (29972)------------------------------
% 1.39/0.58  % (29972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (29972)Termination reason: Refutation
% 1.39/0.58  
% 1.39/0.58  % (29972)Memory used [KB]: 11257
% 1.39/0.58  % (29972)Time elapsed: 0.169 s
% 1.39/0.58  % (29972)------------------------------
% 1.39/0.58  % (29972)------------------------------
% 1.39/0.58  % (29954)Success in time 0.216 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:51:26 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   61 (  84 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 174 expanded)
%              Number of equality atoms :   46 (  65 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f143,f165,f252,f279])).

fof(f279,plain,
    ( ~ spl2_1
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl2_1
    | spl2_10 ),
    inference(unit_resulting_resolution,[],[f48,f43,f251,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X0),X1) = k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X0),X1) = k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

fof(f251,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl2_10
  <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f252,plain,
    ( ~ spl2_1
    | ~ spl2_10
    | spl2_6 ),
    inference(avatar_split_clause,[],[f243,f140,f249,f46])).

fof(f140,plain,
    ( spl2_6
  <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f243,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(superposition,[],[f142,f98])).

fof(f98,plain,(
    ! [X8,X9] :
      ( k6_subset_1(k1_relat_1(X8),X9) = k5_xboole_0(k1_relat_1(X8),k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f42,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f142,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f165,plain,
    ( ~ spl2_1
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl2_1
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f48,f138,f97])).

fof(f97,plain,(
    ! [X6,X7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X6,X7)),k1_relat_1(X6))
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f37,f35])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f138,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_5
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f143,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | spl2_2 ),
    inference(avatar_split_clause,[],[f131,f51,f140,f136])).

fof(f51,plain,
    ( spl2_2
  <=> k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f131,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | spl2_2 ),
    inference(superposition,[],[f53,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = k5_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f42,f59])).

fof(f59,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f36,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f49,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:11:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (26675)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (26653)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (26656)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (26659)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.52  % (26662)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.53  % (26664)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.53  % (26681)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.22/0.53  % (26662)Refutation not found, incomplete strategy% (26662)------------------------------
% 1.22/0.53  % (26662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (26662)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (26662)Memory used [KB]: 10618
% 1.22/0.53  % (26662)Time elapsed: 0.106 s
% 1.22/0.53  % (26662)------------------------------
% 1.22/0.53  % (26662)------------------------------
% 1.22/0.54  % (26658)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.54  % (26675)Refutation found. Thanks to Tanya!
% 1.22/0.54  % SZS status Theorem for theBenchmark
% 1.22/0.54  % (26660)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.22/0.54  % (26678)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.54  % (26657)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.54  % (26674)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.54  % (26670)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.54  % (26672)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.54  % (26673)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.54  % (26676)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.55  % (26654)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.35/0.55  % (26681)Refutation not found, incomplete strategy% (26681)------------------------------
% 1.35/0.55  % (26681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (26681)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (26681)Memory used [KB]: 1663
% 1.35/0.55  % (26681)Time elapsed: 0.103 s
% 1.35/0.55  % (26681)------------------------------
% 1.35/0.55  % (26681)------------------------------
% 1.35/0.55  % (26680)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.55  % (26665)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.35/0.55  % (26680)Refutation not found, incomplete strategy% (26680)------------------------------
% 1.35/0.55  % (26680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (26680)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (26680)Memory used [KB]: 10618
% 1.35/0.55  % (26680)Time elapsed: 0.139 s
% 1.35/0.55  % (26680)------------------------------
% 1.35/0.55  % (26680)------------------------------
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f280,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(avatar_sat_refutation,[],[f49,f54,f143,f165,f252,f279])).
% 1.35/0.55  fof(f279,plain,(
% 1.35/0.55    ~spl2_1 | spl2_10),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f264])).
% 1.35/0.55  fof(f264,plain,(
% 1.35/0.55    $false | (~spl2_1 | spl2_10)),
% 1.35/0.55    inference(unit_resulting_resolution,[],[f48,f43,f251,f160])).
% 1.35/0.55  fof(f160,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k6_subset_1(k1_relat_1(X0),X1) = k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0))) )),
% 1.35/0.55    inference(duplicate_literal_removal,[],[f155])).
% 1.35/0.55  fof(f155,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k6_subset_1(k1_relat_1(X0),X1) = k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.35/0.55    inference(superposition,[],[f33,f32])).
% 1.35/0.55  fof(f32,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.35/0.55    inference(flattening,[],[f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 1.35/0.55    inference(ennf_transformation,[],[f15])).
% 1.35/0.55  fof(f15,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f14])).
% 1.35/0.55  fof(f14,axiom,(
% 1.35/0.55    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).
% 1.35/0.55  fof(f251,plain,(
% 1.35/0.55    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) | spl2_10),
% 1.35/0.55    inference(avatar_component_clause,[],[f249])).
% 1.35/0.55  fof(f249,plain,(
% 1.35/0.55    spl2_10 <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.35/0.55  fof(f43,plain,(
% 1.35/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.35/0.55    inference(equality_resolution,[],[f39])).
% 1.35/0.55  fof(f39,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f28])).
% 1.35/0.55  fof(f28,plain,(
% 1.35/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.55    inference(flattening,[],[f27])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f2])).
% 1.35/0.55  fof(f2,axiom,(
% 1.35/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.35/0.55  fof(f48,plain,(
% 1.35/0.55    v1_relat_1(sK1) | ~spl2_1),
% 1.35/0.55    inference(avatar_component_clause,[],[f46])).
% 1.35/0.55  fof(f46,plain,(
% 1.35/0.55    spl2_1 <=> v1_relat_1(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.35/0.55  fof(f252,plain,(
% 1.35/0.55    ~spl2_1 | ~spl2_10 | spl2_6),
% 1.35/0.55    inference(avatar_split_clause,[],[f243,f140,f249,f46])).
% 1.35/0.55  fof(f140,plain,(
% 1.35/0.55    spl2_6 <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.35/0.55  fof(f243,plain,(
% 1.35/0.55    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | spl2_6),
% 1.35/0.55    inference(superposition,[],[f142,f98])).
% 1.35/0.55  fof(f98,plain,(
% 1.35/0.55    ( ! [X8,X9] : (k6_subset_1(k1_relat_1(X8),X9) = k5_xboole_0(k1_relat_1(X8),k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(X8)) )),
% 1.35/0.55    inference(superposition,[],[f42,f35])).
% 1.35/0.55  fof(f35,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f23])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f16])).
% 1.35/0.55  fof(f16,axiom,(
% 1.35/0.55    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.35/0.55  fof(f42,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f41,f34])).
% 1.35/0.55  fof(f34,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f12])).
% 1.35/0.55  fof(f12,axiom,(
% 1.35/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.35/0.55  fof(f41,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f3])).
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.35/0.55  fof(f142,plain,(
% 1.35/0.55    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) | spl2_6),
% 1.35/0.55    inference(avatar_component_clause,[],[f140])).
% 1.35/0.55  fof(f165,plain,(
% 1.35/0.55    ~spl2_1 | spl2_5),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f163])).
% 1.35/0.55  fof(f163,plain,(
% 1.35/0.55    $false | (~spl2_1 | spl2_5)),
% 1.35/0.55    inference(unit_resulting_resolution,[],[f48,f138,f97])).
% 1.35/0.55  fof(f97,plain,(
% 1.35/0.55    ( ! [X6,X7] : (r1_tarski(k1_relat_1(k7_relat_1(X6,X7)),k1_relat_1(X6)) | ~v1_relat_1(X6)) )),
% 1.35/0.55    inference(superposition,[],[f37,f35])).
% 1.35/0.55  fof(f37,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.35/0.55  fof(f138,plain,(
% 1.35/0.55    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | spl2_5),
% 1.35/0.55    inference(avatar_component_clause,[],[f136])).
% 1.35/0.55  fof(f136,plain,(
% 1.35/0.55    spl2_5 <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.35/0.55  fof(f143,plain,(
% 1.35/0.55    ~spl2_5 | ~spl2_6 | spl2_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f131,f51,f140,f136])).
% 1.35/0.55  fof(f51,plain,(
% 1.35/0.55    spl2_2 <=> k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.35/0.55  fof(f131,plain,(
% 1.35/0.55    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | spl2_2),
% 1.35/0.55    inference(superposition,[],[f53,f76])).
% 1.35/0.55  fof(f76,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.35/0.55    inference(superposition,[],[f42,f59])).
% 1.35/0.55  fof(f59,plain,(
% 1.35/0.55    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.35/0.55    inference(superposition,[],[f36,f31])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.55  fof(f36,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.35/0.55  fof(f53,plain,(
% 1.35/0.55    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) | spl2_2),
% 1.35/0.55    inference(avatar_component_clause,[],[f51])).
% 1.35/0.55  fof(f54,plain,(
% 1.35/0.55    ~spl2_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f30,f51])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 1.35/0.55    inference(cnf_transformation,[],[f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f19,plain,(
% 1.35/0.55    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f18])).
% 1.35/0.55  fof(f18,negated_conjecture,(
% 1.35/0.55    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.35/0.55    inference(negated_conjecture,[],[f17])).
% 1.35/0.55  fof(f17,conjecture,(
% 1.35/0.55    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 1.35/0.55  fof(f49,plain,(
% 1.35/0.55    spl2_1),
% 1.35/0.55    inference(avatar_split_clause,[],[f29,f46])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    v1_relat_1(sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f26])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (26675)------------------------------
% 1.35/0.55  % (26675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (26675)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (26675)Memory used [KB]: 10874
% 1.35/0.55  % (26675)Time elapsed: 0.121 s
% 1.35/0.55  % (26675)------------------------------
% 1.35/0.55  % (26675)------------------------------
% 1.35/0.55  % (26666)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.35/0.55  % (26651)Success in time 0.187 s
%------------------------------------------------------------------------------

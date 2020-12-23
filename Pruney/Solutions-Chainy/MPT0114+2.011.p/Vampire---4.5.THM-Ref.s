%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 118 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 306 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f51,f62,f64,f67,f244])).

fof(f244,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f239,f43])).

fof(f43,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f239,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f238,f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f238,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
        | ~ r1_tarski(sK0,X1) )
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f236,f70])).

fof(f70,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f50,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f50,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f236,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK0,X1)
        | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) )
    | ~ spl3_3 ),
    inference(resolution,[],[f85,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f85,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f82,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f30,f70])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

% (6244)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% (6254)Refutation not found, incomplete strategy% (6254)------------------------------
% (6254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6254)Termination reason: Refutation not found, incomplete strategy

% (6254)Memory used [KB]: 10746
% (6254)Time elapsed: 0.070 s
% (6254)------------------------------
% (6254)------------------------------
% (6249)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (6255)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f82,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
      | r1_tarski(X8,k2_xboole_0(X6,k4_xboole_0(X7,X6))) ) ),
    inference(superposition,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f23,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

% (6252)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f67,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f53,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f64,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f62,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f33,f48,f41,f37])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f21,f22,f31])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f51,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f34,f48,f37])).

fof(f34,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f20,f22,f31])).

fof(f20,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f41,f37])).

fof(f35,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f19,f31])).

fof(f19,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:33:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (6246)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (6247)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (6251)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (6245)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (6256)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (6259)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (6245)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (6248)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (6243)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (6254)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (6253)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f44,f51,f62,f64,f67,f244])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f243])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(resolution,[],[f239,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | (spl3_1 | ~spl3_3)),
% 0.22/0.51    inference(resolution,[],[f238,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ~r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(sK0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | ~r1_tarski(sK0,X1)) ) | ~spl3_3),
% 0.22/0.51    inference(forward_demodulation,[],[f236,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f50,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl3_3 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(sK0,X1) | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f85,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) | ~r1_tarski(sK0,X0)) ) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f82,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) | ~r1_tarski(sK0,X0)) ) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f30,f70])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  % (6244)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (6254)Refutation not found, incomplete strategy% (6254)------------------------------
% 0.22/0.52  % (6254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6254)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6254)Memory used [KB]: 10746
% 0.22/0.52  % (6254)Time elapsed: 0.070 s
% 0.22/0.52  % (6254)------------------------------
% 0.22/0.52  % (6254)------------------------------
% 0.22/0.52  % (6249)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6255)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X6,X8,X7] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | r1_tarski(X8,k2_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 0.22/0.53    inference(superposition,[],[f28,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f23,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f24,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.53  % (6252)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    $false | (~spl3_1 | spl3_2)),
% 0.22/0.53    inference(resolution,[],[f53,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f41])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f39,f28])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f37])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~spl3_1 | spl3_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    $false | (~spl3_1 | spl3_3)),
% 0.22/0.53    inference(resolution,[],[f49,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f39,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f48])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f48,f41,f37])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.22/0.53    inference(definition_unfolding,[],[f21,f22,f31])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 0.22/0.53    inference(nnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl3_1 | spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f48,f37])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.22/0.53    inference(definition_unfolding,[],[f20,f22,f31])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f41,f37])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.22/0.53    inference(definition_unfolding,[],[f19,f31])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (6245)------------------------------
% 0.22/0.53  % (6245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6245)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (6245)Memory used [KB]: 6268
% 0.22/0.53  % (6245)Time elapsed: 0.066 s
% 0.22/0.53  % (6245)------------------------------
% 0.22/0.53  % (6245)------------------------------
% 0.22/0.53  % (6258)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.53  % (6242)Success in time 0.163 s
%------------------------------------------------------------------------------

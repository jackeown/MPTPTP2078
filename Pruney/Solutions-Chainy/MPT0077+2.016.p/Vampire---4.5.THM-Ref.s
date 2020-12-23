%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 131 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 ( 351 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f53,f166,f241,f411])).

fof(f411,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f243,f405])).

fof(f405,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f245,f340])).

fof(f340,plain,
    ( ! [X4] : k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k3_xboole_0(sK0,X4)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f337,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f337,plain,
    ( ! [X4] : k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X4))
    | ~ spl3_3 ),
    inference(superposition,[],[f32,f259])).

fof(f259,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_3 ),
    inference(superposition,[],[f37,f254])).

fof(f254,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f176,f57])).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f176,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f33,f171])).

fof(f171,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f51,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f245,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f243,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f241,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f77,f235])).

fof(f235,plain,
    ( ! [X2] : k1_xboole_0 != k3_xboole_0(k2_xboole_0(X2,sK2),sK0)
    | spl3_1 ),
    inference(resolution,[],[f207,f36])).

fof(f207,plain,
    ( ! [X1] : ~ r1_xboole_0(k2_xboole_0(X1,sK2),sK0)
    | spl3_1 ),
    inference(resolution,[],[f172,f60])).

fof(f60,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_xboole_0(X0,sK0) )
    | spl3_1 ),
    inference(resolution,[],[f169,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f169,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl3_1 ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f41,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f77,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f35,f34])).

fof(f166,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f77,f160])).

fof(f160,plain,
    ( ! [X2] : k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK1,X2),sK0)
    | spl3_3 ),
    inference(resolution,[],[f156,f36])).

fof(f156,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK1,X0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f126,f30])).

fof(f126,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ r1_xboole_0(X1,sK0) )
    | spl3_3 ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl3_3 ),
    inference(resolution,[],[f34,f50])).

fof(f50,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f53,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f40,f49,f44])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f52,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f44,f49])).

fof(f25,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f26,f44,f40])).

fof(f26,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:05:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (4876)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (4875)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (4874)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (4880)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (4884)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (4883)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (4877)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (4882)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (4885)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (4887)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (4879)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (4888)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (4883)Refutation not found, incomplete strategy% (4883)------------------------------
% 0.22/0.50  % (4883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4883)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (4883)Memory used [KB]: 10618
% 0.22/0.50  % (4883)Time elapsed: 0.077 s
% 0.22/0.50  % (4883)------------------------------
% 0.22/0.50  % (4883)------------------------------
% 0.22/0.51  % (4888)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f413,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f47,f52,f53,f166,f241,f411])).
% 0.22/0.51  fof(f411,plain,(
% 0.22/0.51    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f410])).
% 0.22/0.51  fof(f410,plain,(
% 0.22/0.51    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f243,f405])).
% 0.22/0.51  fof(f405,plain,(
% 0.22/0.51    k1_xboole_0 != k3_xboole_0(sK0,sK2) | (spl3_2 | ~spl3_3)),
% 0.22/0.51    inference(superposition,[],[f245,f340])).
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    ( ! [X4] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k3_xboole_0(sK0,X4)) ) | ~spl3_3),
% 0.22/0.51    inference(forward_demodulation,[],[f337,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    ( ! [X4] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X4))) ) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f32,f259])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f37,f254])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f176,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.51    inference(superposition,[],[f31,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 0.22/0.51    inference(superposition,[],[f33,f171])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f51,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.22/0.51    inference(resolution,[],[f45,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl3_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f42,f35])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    spl3_1 | ~spl3_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    $false | (spl3_1 | ~spl3_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f77,f235])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ( ! [X2] : (k1_xboole_0 != k3_xboole_0(k2_xboole_0(X2,sK2),sK0)) ) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f207,f36])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_xboole_0(k2_xboole_0(X1,sK2),sK0)) ) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f172,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.22/0.51    inference(superposition,[],[f30,f31])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_xboole_0(X0,sK0)) ) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f169,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ~r1_xboole_0(sK2,sK0) | spl3_1),
% 0.22/0.51    inference(resolution,[],[f41,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f40])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f73,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(resolution,[],[f35,f34])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ~spl3_2 | spl3_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    $false | (~spl3_2 | spl3_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f77,f160])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ( ! [X2] : (k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK1,X2),sK0)) ) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f156,f36])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK1,X0),sK0)) ) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f126,f30])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(sK1,X1) | ~r1_xboole_0(X1,sK0)) ) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f38,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~r1_xboole_0(sK1,sK0) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f34,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f49])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ~spl3_2 | ~spl3_3 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f40,f49,f44])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl3_3 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f44,f49])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f44,f40])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (4888)------------------------------
% 0.22/0.53  % (4888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4888)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (4888)Memory used [KB]: 6396
% 0.22/0.53  % (4888)Time elapsed: 0.085 s
% 0.22/0.53  % (4888)------------------------------
% 0.22/0.53  % (4888)------------------------------
% 0.22/0.53  % (4871)Success in time 0.166 s
%------------------------------------------------------------------------------

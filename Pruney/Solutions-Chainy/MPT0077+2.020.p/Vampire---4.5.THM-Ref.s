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
% DateTime   : Thu Dec  3 12:30:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 266 expanded)
%              Number of leaves         :   12 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 ( 492 expanded)
%              Number of equality atoms :   48 ( 222 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f736,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f42,f376,f383,f733])).

fof(f733,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f732])).

fof(f732,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f384,f722])).

fof(f722,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f386,f548])).

fof(f548,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f537,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f537,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_3 ),
    inference(superposition,[],[f22,f453])).

fof(f453,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_3 ),
    inference(superposition,[],[f27,f443])).

fof(f443,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f392,f52])).

fof(f52,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f49,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f24,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f392,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f24,f385])).

fof(f385,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f40,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f40,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f386,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f384,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f383,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f373,f381])).

fof(f381,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(resolution,[],[f30,f26])).

fof(f30,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f373,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f362,f20])).

fof(f362,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f349,f115])).

fof(f115,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f105,f23])).

fof(f105,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f27,f84])).

fof(f84,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f82,f20])).

fof(f82,plain,(
    ! [X2] : k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f22,f55])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f52,f49])).

fof(f349,plain,
    ( ! [X3] : k3_xboole_0(sK0,k4_xboole_0(X3,k2_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,X3)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f340,f278])).

fof(f278,plain,
    ( ! [X6] : k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X6)) = k3_xboole_0(sK0,X6)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f271,f22])).

fof(f271,plain,
    ( ! [X6] : k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X6)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X6))
    | ~ spl3_2 ),
    inference(superposition,[],[f22,f100])).

fof(f100,plain,
    ( ! [X7] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X7)) = k4_xboole_0(sK0,X7)
    | ~ spl3_2 ),
    inference(superposition,[],[f27,f54])).

fof(f54,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2 ),
    inference(superposition,[],[f24,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f340,plain,
    ( ! [X3] : k3_xboole_0(sK0,k4_xboole_0(X3,k2_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X3))
    | ~ spl3_2 ),
    inference(superposition,[],[f278,f23])).

fof(f376,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f44,f374])).

fof(f374,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f363,f20])).

fof(f363,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f349,f119])).

fof(f119,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f115,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f44,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f42,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f29,f38,f33])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
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

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f41,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f18,f33,f38])).

fof(f18,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f19,f33,f29])).

fof(f19,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (27970)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (27975)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (27981)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (27986)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (27977)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (27985)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (27981)Refutation not found, incomplete strategy% (27981)------------------------------
% 0.20/0.47  % (27981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27984)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (27973)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (27978)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (27981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (27981)Memory used [KB]: 10618
% 0.20/0.47  % (27981)Time elapsed: 0.067 s
% 0.20/0.47  % (27981)------------------------------
% 0.20/0.47  % (27981)------------------------------
% 0.20/0.47  % (27983)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (27974)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (27976)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (27972)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (27987)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (27979)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (27982)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (27980)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (27971)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (27986)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f736,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f36,f41,f42,f376,f383,f733])).
% 0.20/0.50  fof(f733,plain,(
% 0.20/0.50    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f732])).
% 0.20/0.50  fof(f732,plain,(
% 0.20/0.50    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f384,f722])).
% 0.20/0.50  fof(f722,plain,(
% 0.20/0.50    k1_xboole_0 != k3_xboole_0(sK0,sK2) | (spl3_2 | ~spl3_3)),
% 0.20/0.50    inference(superposition,[],[f386,f548])).
% 0.20/0.50  fof(f548,plain,(
% 0.20/0.50    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_3),
% 0.20/0.50    inference(forward_demodulation,[],[f537,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f537,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_3),
% 0.20/0.50    inference(superposition,[],[f22,f453])).
% 0.20/0.50  fof(f453,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_3),
% 0.20/0.50    inference(superposition,[],[f27,f443])).
% 0.20/0.50  fof(f443,plain,(
% 0.20/0.50    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.20/0.50    inference(superposition,[],[f392,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.20/0.50    inference(superposition,[],[f49,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.50    inference(superposition,[],[f24,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 0.20/0.50    inference(superposition,[],[f24,f385])).
% 0.20/0.50  fof(f385,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f40,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    r1_xboole_0(sK0,sK1) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.50  fof(f386,plain,(
% 0.20/0.50    k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.20/0.50    inference(resolution,[],[f34,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    spl3_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f384,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_1),
% 0.20/0.50    inference(resolution,[],[f31,f25])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f382])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f373,f381])).
% 0.20/0.50  fof(f381,plain,(
% 0.20/0.50    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_1),
% 0.20/0.50    inference(resolution,[],[f30,f26])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ~r1_xboole_0(sK0,sK2) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f29])).
% 0.20/0.50  fof(f373,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.50    inference(forward_demodulation,[],[f362,f20])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f349,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f105,f23])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 0.20/0.50    inference(superposition,[],[f27,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f82,f20])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X2] : (k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2)) )),
% 0.20/0.50    inference(superposition,[],[f22,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(superposition,[],[f52,f49])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    ( ! [X3] : (k3_xboole_0(sK0,k4_xboole_0(X3,k2_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,X3)) ) | ~spl3_2),
% 0.20/0.50    inference(forward_demodulation,[],[f340,f278])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    ( ! [X6] : (k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X6)) = k3_xboole_0(sK0,X6)) ) | ~spl3_2),
% 0.20/0.50    inference(forward_demodulation,[],[f271,f22])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ( ! [X6] : (k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X6)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X6))) ) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f22,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X7] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X7)) = k4_xboole_0(sK0,X7)) ) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f27,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f52,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f24,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f25,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f33])).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    ( ! [X3] : (k3_xboole_0(sK0,k4_xboole_0(X3,k2_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X3))) ) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f278,f23])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    ~spl3_2 | spl3_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f375])).
% 0.20/0.50  fof(f375,plain,(
% 0.20/0.50    $false | (~spl3_2 | spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f44,f374])).
% 0.20/0.50  fof(f374,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.50    inference(forward_demodulation,[],[f363,f20])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) | ~spl3_2),
% 0.20/0.50    inference(superposition,[],[f349,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 0.20/0.50    inference(superposition,[],[f115,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl3_3),
% 0.20/0.50    inference(resolution,[],[f26,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f38])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ~spl3_2 | ~spl3_3 | ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f14,f29,f38,f33])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f8])).
% 0.20/0.50  fof(f8,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    spl3_3 | spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f18,f33,f38])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    spl3_1 | spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f19,f33,f29])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (27986)------------------------------
% 0.20/0.50  % (27986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27986)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (27986)Memory used [KB]: 6524
% 0.20/0.50  % (27986)Time elapsed: 0.077 s
% 0.20/0.50  % (27986)------------------------------
% 0.20/0.50  % (27986)------------------------------
% 0.20/0.51  % (27969)Success in time 0.152 s
%------------------------------------------------------------------------------

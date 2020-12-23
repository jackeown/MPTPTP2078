%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 236 expanded)
%              Number of leaves         :   17 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 368 expanded)
%              Number of equality atoms :   47 ( 179 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4028,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f60,f149,f150,f3793,f4017])).

fof(f4017,plain,
    ( spl3_1
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f4016])).

fof(f4016,plain,
    ( $false
    | spl3_1
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f3958,f39])).

fof(f39,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f3958,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(superposition,[],[f1263,f3792])).

fof(f3792,plain,
    ( sK0 = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f3790])).

fof(f3790,plain,
    ( spl3_24
  <=> sK0 = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1263,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f248,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f75,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f34,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f30,f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f248,plain,
    ( ! [X10,X8,X9] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k5_xboole_0(X9,k3_xboole_0(X9,X10)))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f222,f247])).

fof(f247,plain,
    ( ! [X7] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,k1_xboole_0))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f221,f246])).

fof(f246,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f242,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f242,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f158,f238])).

fof(f238,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f143,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f143,plain,(
    ! [X8] : r1_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f76,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(unit_resulting_resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f76,plain,(
    ! [X4,X5,X3] : r1_xboole_0(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),X5) ),
    inference(superposition,[],[f32,f35])).

fof(f158,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f35,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f221,plain,
    ( ! [X7] : k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X7))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,k1_xboole_0))
    | ~ spl3_5 ),
    inference(superposition,[],[f73,f79])).

fof(f73,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f35,f23])).

fof(f222,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k5_xboole_0(X9,k3_xboole_0(X9,X10))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X10,k1_xboole_0)) ),
    inference(superposition,[],[f73,f54])).

fof(f3793,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f975,f78,f57,f3790])).

fof(f57,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f975,plain,
    ( sK0 = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f936,f21])).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f936,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f204,f246])).

fof(f204,plain,
    ( ! [X6] : k5_xboole_0(sK0,k3_xboole_0(sK0,X6)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,X6)))
    | ~ spl3_4 ),
    inference(superposition,[],[f71,f59])).

fof(f59,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f71,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
    inference(superposition,[],[f35,f23])).

fof(f150,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f142,f57,f41])).

fof(f41,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f142,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f76,f59])).

fof(f149,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f82,f142])).

fof(f82,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f80,f26])).

fof(f80,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f60,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f52,f46,f57])).

fof(f46,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f46])).

fof(f31,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f18,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f41,f37])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (26203)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (26193)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (26191)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (26192)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (26196)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (26198)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (26199)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (26200)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (26201)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (26204)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (26190)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (26194)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (26188)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.55  % (26203)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (26202)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f4028,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f44,f49,f60,f149,f150,f3793,f4017])).
% 0.21/0.56  fof(f4017,plain,(
% 0.21/0.56    spl3_1 | ~spl3_5 | ~spl3_24),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f4016])).
% 0.21/0.56  fof(f4016,plain,(
% 0.21/0.56    $false | (spl3_1 | ~spl3_5 | ~spl3_24)),
% 0.21/0.56    inference(subsumption_resolution,[],[f3958,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.56  fof(f3958,plain,(
% 0.21/0.56    r1_tarski(sK0,sK1) | (~spl3_5 | ~spl3_24)),
% 0.21/0.56    inference(superposition,[],[f1263,f3792])).
% 0.21/0.56  fof(f3792,plain,(
% 0.21/0.56    sK0 = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) | ~spl3_24),
% 0.21/0.56    inference(avatar_component_clause,[],[f3790])).
% 0.21/0.56  fof(f3790,plain,(
% 0.21/0.56    spl3_24 <=> sK0 = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.56  fof(f1263,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X0)) ) | ~spl3_5),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f248,f187])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.56    inference(superposition,[],[f75,f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.56    inference(superposition,[],[f34,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f30,f24,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f28,f24])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.56  fof(f248,plain,(
% 0.21/0.56    ( ! [X10,X8,X9] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k5_xboole_0(X9,k3_xboole_0(X9,X10)))) ) | ~spl3_5),
% 0.21/0.56    inference(backward_demodulation,[],[f222,f247])).
% 0.21/0.56  fof(f247,plain,(
% 0.21/0.56    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,k1_xboole_0))) ) | ~spl3_5),
% 0.21/0.56    inference(backward_demodulation,[],[f221,f246])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) ) | ~spl3_5),
% 0.21/0.56    inference(forward_demodulation,[],[f242,f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) ) | ~spl3_5),
% 0.21/0.56    inference(backward_demodulation,[],[f158,f238])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f143,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    ( ! [X8] : (r1_xboole_0(k1_xboole_0,X8)) )),
% 0.21/0.56    inference(superposition,[],[f76,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f32,f26])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f22,f24])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (r1_xboole_0(k3_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5))),X5)) )),
% 0.21/0.56    inference(superposition,[],[f32,f35])).
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) ) | ~spl3_5),
% 0.21/0.56    inference(superposition,[],[f35,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.56  fof(f221,plain,(
% 0.21/0.56    ( ! [X7] : (k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X7))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,k1_xboole_0))) ) | ~spl3_5),
% 0.21/0.56    inference(superposition,[],[f73,f79])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1)))) )),
% 0.21/0.56    inference(superposition,[],[f35,f23])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    ( ! [X10,X8,X9] : (k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k5_xboole_0(X9,k3_xboole_0(X9,X10))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X10,k1_xboole_0))) )),
% 0.21/0.56    inference(superposition,[],[f73,f54])).
% 0.21/0.56  fof(f3793,plain,(
% 0.21/0.56    spl3_24 | ~spl3_4 | ~spl3_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f975,f78,f57,f3790])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    spl3_4 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.56  fof(f975,plain,(
% 0.21/0.56    sK0 = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) | (~spl3_4 | ~spl3_5)),
% 0.21/0.56    inference(forward_demodulation,[],[f936,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.56  fof(f936,plain,(
% 0.21/0.56    k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k1_xboole_0)) | (~spl3_4 | ~spl3_5)),
% 0.21/0.56    inference(superposition,[],[f204,f246])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    ( ! [X6] : (k5_xboole_0(sK0,k3_xboole_0(sK0,X6)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,X6)))) ) | ~spl3_4),
% 0.21/0.56    inference(superposition,[],[f71,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f57])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) )),
% 0.21/0.56    inference(superposition,[],[f35,f23])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    spl3_2 | ~spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f142,f57,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    r1_xboole_0(sK0,sK2) | ~spl3_4),
% 0.21/0.56    inference(superposition,[],[f76,f59])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    ~spl3_4 | spl3_5),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    $false | (~spl3_4 | spl3_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f82,f142])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ~r1_xboole_0(sK0,sK2) | spl3_5),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f80,f26])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f78])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    spl3_4 | ~spl3_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f52,f46,f57])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f48,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f46])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    spl3_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f31,f46])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.21/0.56    inference(definition_unfolding,[],[f18,f24])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.56    inference(negated_conjecture,[],[f10])).
% 0.21/0.56  fof(f10,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ~spl3_1 | ~spl3_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f19,f41,f37])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (26203)------------------------------
% 0.21/0.56  % (26203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26203)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (26203)Memory used [KB]: 14072
% 0.21/0.56  % (26203)Time elapsed: 0.121 s
% 0.21/0.56  % (26203)------------------------------
% 0.21/0.56  % (26203)------------------------------
% 0.21/0.56  % (26187)Success in time 0.2 s
%------------------------------------------------------------------------------

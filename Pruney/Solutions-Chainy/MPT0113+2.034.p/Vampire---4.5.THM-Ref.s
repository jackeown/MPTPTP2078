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
% DateTime   : Thu Dec  3 12:32:37 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 143 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 264 expanded)
%              Number of equality atoms :   59 ( 101 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f87,f101,f112,f139,f140,f150,f2409,f3292,f3319])).

fof(f3319,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    | sK0 != k3_xboole_0(sK0,sK0)
    | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3292,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f3245,f108,f83,f3288])).

fof(f3288,plain,
    ( spl3_20
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f83,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f108,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f3245,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f85,f2581])).

fof(f2581,plain,
    ( ! [X9] : k3_xboole_0(sK0,X9) = k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f2580,f64])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f38,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f2580,plain,
    ( ! [X9] : k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X9),k1_xboole_0)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f2579,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2579,plain,
    ( ! [X9] : k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X9),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X9)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f2539,f159])).

fof(f159,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f35,f28])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f2539,plain,
    ( ! [X9] : k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X9),k3_xboole_0(sK0,k3_xboole_0(X9,k1_xboole_0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f176,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f176,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2)))) ),
    inference(forward_demodulation,[],[f42,f35])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f36,f29,f29])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f85,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f2409,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2408,f83,f108])).

fof(f2408,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2342,f23])).

fof(f2342,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f157,f88])).

fof(f88,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(unit_resulting_resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f157,plain,
    ( ! [X14] : k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X14)) = k3_xboole_0(sK0,X14)
    | ~ spl3_4 ),
    inference(superposition,[],[f35,f85])).

fof(f150,plain,
    ( ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f142,f44,f146])).

fof(f146,plain,
    ( spl3_9
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f44,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f142,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f140,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f128,f98,f130])).

fof(f130,plain,
    ( spl3_7
  <=> sK0 = k3_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f98,plain,
    ( spl3_5
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f128,plain,
    ( sK0 = k3_xboole_0(sK0,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f100,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f100,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f139,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f127,f98,f135])).

fof(f135,plain,
    ( spl3_8
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f127,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | ~ spl3_5 ),
    inference(resolution,[],[f100,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f112,plain,
    ( ~ spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f105,f48,f108])).

fof(f48,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f105,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(resolution,[],[f32,f50])).

fof(f50,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f101,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f95,f83,f98])).

fof(f95,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f27,f85])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f87,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f79,f53,f83])).

fof(f53,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f30,f55])).

fof(f55,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f53])).

fof(f37,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f21,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f51,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f48,f44])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:53:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (25754)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.44  % (25756)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (25755)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (25760)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (25748)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (25757)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (25749)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (25744)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (25752)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (25751)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (25747)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (25753)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (25745)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (25750)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (25758)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (25761)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (25746)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.53  % (25759)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.57/0.60  % (25750)Refutation found. Thanks to Tanya!
% 1.57/0.60  % SZS status Theorem for theBenchmark
% 1.57/0.62  % SZS output start Proof for theBenchmark
% 1.57/0.62  fof(f3320,plain,(
% 1.57/0.62    $false),
% 1.57/0.62    inference(avatar_sat_refutation,[],[f51,f56,f87,f101,f112,f139,f140,f150,f2409,f3292,f3319])).
% 1.57/0.62  fof(f3319,plain,(
% 1.57/0.62    sK0 != k3_xboole_0(sK0,sK1) | sK0 != k3_xboole_0(sK0,sK0) | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.57/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.62  fof(f3292,plain,(
% 1.57/0.62    spl3_20 | ~spl3_4 | ~spl3_6),
% 1.57/0.62    inference(avatar_split_clause,[],[f3245,f108,f83,f3288])).
% 1.57/0.62  fof(f3288,plain,(
% 1.57/0.62    spl3_20 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.57/0.62  fof(f83,plain,(
% 1.57/0.62    spl3_4 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.57/0.62  fof(f108,plain,(
% 1.57/0.62    spl3_6 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.57/0.62  fof(f3245,plain,(
% 1.57/0.62    sK0 = k3_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_6)),
% 1.57/0.62    inference(superposition,[],[f85,f2581])).
% 1.57/0.62  fof(f2581,plain,(
% 1.57/0.62    ( ! [X9] : (k3_xboole_0(sK0,X9) = k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2)))) ) | ~spl3_6),
% 1.57/0.62    inference(forward_demodulation,[],[f2580,f64])).
% 1.57/0.62  fof(f64,plain,(
% 1.57/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.62    inference(forward_demodulation,[],[f38,f23])).
% 1.57/0.62  fof(f23,plain,(
% 1.57/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f8])).
% 1.57/0.62  fof(f8,axiom,(
% 1.57/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.57/0.62  fof(f38,plain,(
% 1.57/0.62    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.57/0.62    inference(definition_unfolding,[],[f25,f29])).
% 1.57/0.62  fof(f29,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.62    inference(cnf_transformation,[],[f4])).
% 1.57/0.62  fof(f4,axiom,(
% 1.57/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.62  fof(f25,plain,(
% 1.57/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.62    inference(cnf_transformation,[],[f9])).
% 1.57/0.62  fof(f9,axiom,(
% 1.57/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.57/0.62  fof(f2580,plain,(
% 1.57/0.62    ( ! [X9] : (k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X9),k1_xboole_0)) ) | ~spl3_6),
% 1.57/0.62    inference(forward_demodulation,[],[f2579,f58])).
% 1.57/0.62  fof(f58,plain,(
% 1.57/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.62    inference(superposition,[],[f28,f23])).
% 1.57/0.62  fof(f28,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f1])).
% 1.57/0.62  fof(f1,axiom,(
% 1.57/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.57/0.62  fof(f2579,plain,(
% 1.57/0.62    ( ! [X9] : (k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X9),k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X9)))) ) | ~spl3_6),
% 1.57/0.62    inference(forward_demodulation,[],[f2539,f159])).
% 1.57/0.62  fof(f159,plain,(
% 1.57/0.62    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 1.57/0.62    inference(superposition,[],[f35,f28])).
% 1.57/0.62  fof(f35,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.57/0.62    inference(cnf_transformation,[],[f5])).
% 1.57/0.62  fof(f5,axiom,(
% 1.57/0.62    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.57/0.62  fof(f2539,plain,(
% 1.57/0.62    ( ! [X9] : (k3_xboole_0(sK0,k5_xboole_0(X9,k3_xboole_0(X9,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X9),k3_xboole_0(sK0,k3_xboole_0(X9,k1_xboole_0)))) ) | ~spl3_6),
% 1.57/0.62    inference(superposition,[],[f176,f109])).
% 1.57/0.62  fof(f109,plain,(
% 1.57/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_6),
% 1.57/0.62    inference(avatar_component_clause,[],[f108])).
% 1.57/0.62  fof(f176,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2))))) )),
% 1.57/0.62    inference(forward_demodulation,[],[f42,f35])).
% 1.57/0.62  fof(f42,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)))) )),
% 1.57/0.62    inference(definition_unfolding,[],[f36,f29,f29])).
% 1.57/0.62  fof(f36,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.57/0.62    inference(cnf_transformation,[],[f10])).
% 1.57/0.62  fof(f10,axiom,(
% 1.57/0.62    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 1.57/0.62  fof(f85,plain,(
% 1.57/0.62    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_4),
% 1.57/0.62    inference(avatar_component_clause,[],[f83])).
% 1.57/0.62  fof(f2409,plain,(
% 1.57/0.62    spl3_6 | ~spl3_4),
% 1.57/0.62    inference(avatar_split_clause,[],[f2408,f83,f108])).
% 1.57/0.62  fof(f2408,plain,(
% 1.57/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_4),
% 1.57/0.62    inference(forward_demodulation,[],[f2342,f23])).
% 1.57/0.62  fof(f2342,plain,(
% 1.57/0.62    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_xboole_0) | ~spl3_4),
% 1.57/0.62    inference(superposition,[],[f157,f88])).
% 1.57/0.62  fof(f88,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f39,f31])).
% 1.57/0.62  fof(f31,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.57/0.62    inference(cnf_transformation,[],[f19])).
% 1.57/0.62  fof(f19,plain,(
% 1.57/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.57/0.62    inference(nnf_transformation,[],[f2])).
% 1.57/0.62  fof(f2,axiom,(
% 1.57/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.57/0.62  fof(f39,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.57/0.62    inference(definition_unfolding,[],[f26,f29])).
% 1.57/0.62  fof(f26,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f11])).
% 1.57/0.62  fof(f11,axiom,(
% 1.57/0.62    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.57/0.62  fof(f157,plain,(
% 1.57/0.62    ( ! [X14] : (k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X14)) = k3_xboole_0(sK0,X14)) ) | ~spl3_4),
% 1.57/0.62    inference(superposition,[],[f35,f85])).
% 1.57/0.62  fof(f150,plain,(
% 1.57/0.62    ~spl3_9 | spl3_1),
% 1.57/0.62    inference(avatar_split_clause,[],[f142,f44,f146])).
% 1.57/0.62  fof(f146,plain,(
% 1.57/0.62    spl3_9 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.57/0.62  fof(f44,plain,(
% 1.57/0.62    spl3_1 <=> r1_tarski(sK0,sK1)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.57/0.62  fof(f142,plain,(
% 1.57/0.62    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl3_1),
% 1.57/0.62    inference(resolution,[],[f41,f46])).
% 1.57/0.62  fof(f46,plain,(
% 1.57/0.62    ~r1_tarski(sK0,sK1) | spl3_1),
% 1.57/0.62    inference(avatar_component_clause,[],[f44])).
% 1.57/0.62  fof(f41,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.62    inference(definition_unfolding,[],[f33,f29])).
% 1.57/0.62  fof(f33,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f20])).
% 1.57/0.62  fof(f20,plain,(
% 1.57/0.62    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.57/0.62    inference(nnf_transformation,[],[f3])).
% 1.57/0.62  fof(f3,axiom,(
% 1.57/0.62    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.57/0.62  fof(f140,plain,(
% 1.57/0.62    spl3_7 | ~spl3_5),
% 1.57/0.62    inference(avatar_split_clause,[],[f128,f98,f130])).
% 1.57/0.62  fof(f130,plain,(
% 1.57/0.62    spl3_7 <=> sK0 = k3_xboole_0(sK0,sK0)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.57/0.62  fof(f98,plain,(
% 1.57/0.62    spl3_5 <=> r1_tarski(sK0,sK0)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.57/0.62  fof(f128,plain,(
% 1.57/0.62    sK0 = k3_xboole_0(sK0,sK0) | ~spl3_5),
% 1.57/0.62    inference(resolution,[],[f100,f30])).
% 1.57/0.62  fof(f30,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.62    inference(cnf_transformation,[],[f16])).
% 1.57/0.62  fof(f16,plain,(
% 1.57/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.62    inference(ennf_transformation,[],[f7])).
% 1.57/0.62  fof(f7,axiom,(
% 1.57/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.62  fof(f100,plain,(
% 1.57/0.62    r1_tarski(sK0,sK0) | ~spl3_5),
% 1.57/0.62    inference(avatar_component_clause,[],[f98])).
% 1.57/0.62  fof(f139,plain,(
% 1.57/0.62    spl3_8 | ~spl3_5),
% 1.57/0.62    inference(avatar_split_clause,[],[f127,f98,f135])).
% 1.57/0.62  fof(f135,plain,(
% 1.57/0.62    spl3_8 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.57/0.62  fof(f127,plain,(
% 1.57/0.62    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | ~spl3_5),
% 1.57/0.62    inference(resolution,[],[f100,f40])).
% 1.57/0.62  fof(f40,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.62    inference(definition_unfolding,[],[f34,f29])).
% 1.57/0.62  fof(f34,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f20])).
% 1.57/0.62  fof(f112,plain,(
% 1.57/0.62    ~spl3_6 | spl3_2),
% 1.57/0.62    inference(avatar_split_clause,[],[f105,f48,f108])).
% 1.57/0.62  fof(f48,plain,(
% 1.57/0.62    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.57/0.62  fof(f105,plain,(
% 1.57/0.62    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_2),
% 1.57/0.62    inference(resolution,[],[f32,f50])).
% 1.57/0.62  fof(f50,plain,(
% 1.57/0.62    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 1.57/0.62    inference(avatar_component_clause,[],[f48])).
% 1.57/0.62  fof(f32,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.57/0.62    inference(cnf_transformation,[],[f19])).
% 1.57/0.62  fof(f101,plain,(
% 1.57/0.62    spl3_5 | ~spl3_4),
% 1.57/0.62    inference(avatar_split_clause,[],[f95,f83,f98])).
% 1.57/0.62  fof(f95,plain,(
% 1.57/0.62    r1_tarski(sK0,sK0) | ~spl3_4),
% 1.57/0.62    inference(superposition,[],[f27,f85])).
% 1.57/0.62  fof(f27,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f6])).
% 1.57/0.62  fof(f6,axiom,(
% 1.57/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.57/0.62  fof(f87,plain,(
% 1.57/0.62    spl3_4 | ~spl3_3),
% 1.57/0.62    inference(avatar_split_clause,[],[f79,f53,f83])).
% 1.57/0.62  fof(f53,plain,(
% 1.57/0.62    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.57/0.62  fof(f79,plain,(
% 1.57/0.62    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 1.57/0.62    inference(resolution,[],[f30,f55])).
% 1.57/0.62  fof(f55,plain,(
% 1.57/0.62    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 1.57/0.62    inference(avatar_component_clause,[],[f53])).
% 1.57/0.62  fof(f56,plain,(
% 1.57/0.62    spl3_3),
% 1.57/0.62    inference(avatar_split_clause,[],[f37,f53])).
% 1.57/0.62  fof(f37,plain,(
% 1.57/0.62    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.57/0.62    inference(definition_unfolding,[],[f21,f29])).
% 1.57/0.62  fof(f21,plain,(
% 1.57/0.62    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.57/0.62    inference(cnf_transformation,[],[f18])).
% 1.57/0.62  fof(f18,plain,(
% 1.57/0.62    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 1.57/0.62  fof(f17,plain,(
% 1.57/0.62    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f15,plain,(
% 1.57/0.62    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.57/0.62    inference(ennf_transformation,[],[f14])).
% 1.57/0.62  fof(f14,negated_conjecture,(
% 1.57/0.62    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.57/0.62    inference(negated_conjecture,[],[f13])).
% 1.57/0.62  fof(f13,conjecture,(
% 1.57/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.57/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.57/0.62  fof(f51,plain,(
% 1.57/0.62    ~spl3_1 | ~spl3_2),
% 1.57/0.62    inference(avatar_split_clause,[],[f22,f48,f44])).
% 1.57/0.62  fof(f22,plain,(
% 1.57/0.62    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.57/0.62    inference(cnf_transformation,[],[f18])).
% 1.57/0.62  % SZS output end Proof for theBenchmark
% 1.57/0.62  % (25750)------------------------------
% 1.57/0.62  % (25750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (25750)Termination reason: Refutation
% 1.57/0.62  
% 1.57/0.62  % (25750)Memory used [KB]: 8699
% 1.57/0.62  % (25750)Time elapsed: 0.196 s
% 1.57/0.62  % (25750)------------------------------
% 1.57/0.62  % (25750)------------------------------
% 1.57/0.62  % (25743)Success in time 0.248 s
%------------------------------------------------------------------------------

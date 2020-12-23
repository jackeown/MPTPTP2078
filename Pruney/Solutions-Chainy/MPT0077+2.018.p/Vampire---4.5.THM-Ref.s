%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 419 expanded)
%              Number of leaves         :   13 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :  186 ( 660 expanded)
%              Number of equality atoms :   57 ( 375 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f55,f453,f460,f474,f509])).

fof(f509,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f507])).

fof(f507,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f502,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f30,f60])).

fof(f60,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f57,f43])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f57,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f26,f43])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f502,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f492,f480])).

fof(f480,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f476,f60])).

fof(f476,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f475])).

fof(f475,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f53,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f492,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | spl3_2 ),
    inference(backward_demodulation,[],[f461,f472])).

fof(f472,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_1 ),
    inference(superposition,[],[f29,f466])).

fof(f466,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f462,f60])).

fof(f462,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f31,f454])).

fof(f454,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f461,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f474,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39,f52])).

fof(f20,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
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

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f460,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2
    | spl3_3 ),
    inference(superposition,[],[f457,f62])).

fof(f457,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(forward_demodulation,[],[f456,f437])).

fof(f437,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f429,f60])).

fof(f429,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f382,f86])).

fof(f86,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f80,f26])).

fof(f80,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f29,f62])).

fof(f382,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f369,f304])).

fof(f304,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_2 ),
    inference(superposition,[],[f29,f287])).

fof(f287,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f262,f60])).

fof(f262,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f31,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f369,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X2))
    | ~ spl3_2 ),
    inference(superposition,[],[f304,f26])).

fof(f456,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_3 ),
    inference(resolution,[],[f54,f32])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f453,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f451])).

fof(f451,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f447,f62])).

fof(f447,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f66,f438])).

fof(f438,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f430,f60])).

fof(f430,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f382,f89])).

fof(f89,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f86,f23])).

fof(f66,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f32,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f55,plain,
    ( ~ spl3_2
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f52,f35,f39])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f19,f39,f35])).

fof(f19,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:08:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3169)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (3166)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (3176)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (3168)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (3179)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (3172)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (3165)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (3177)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (3171)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (3170)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (3174)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (3175)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (3167)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.52  % (3180)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (3166)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f510,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f42,f55,f453,f460,f474,f509])).
% 0.22/0.52  fof(f509,plain,(
% 0.22/0.52    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f508])).
% 0.22/0.52  fof(f508,plain,(
% 0.22/0.52    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f507])).
% 0.22/0.52  fof(f507,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.22/0.52    inference(superposition,[],[f502,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f30,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 0.22/0.52    inference(forward_demodulation,[],[f57,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.52    inference(superposition,[],[f23,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 0.22/0.52    inference(superposition,[],[f26,f43])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f21,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.52  fof(f502,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.22/0.52    inference(forward_demodulation,[],[f492,f480])).
% 0.22/0.52  fof(f480,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.22/0.52    inference(forward_demodulation,[],[f476,f60])).
% 0.22/0.52  fof(f476,plain,(
% 0.22/0.52    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.22/0.52    inference(superposition,[],[f31,f475])).
% 0.22/0.52  fof(f475,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_3),
% 0.22/0.52    inference(resolution,[],[f53,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f27,f24])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    r1_xboole_0(sK0,sK2) | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f25,f24])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.52  fof(f492,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_1 | spl3_2)),
% 0.22/0.52    inference(backward_demodulation,[],[f461,f472])).
% 0.22/0.52  fof(f472,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_1),
% 0.22/0.52    inference(superposition,[],[f29,f466])).
% 0.22/0.52  fof(f466,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.52    inference(forward_demodulation,[],[f462,f60])).
% 0.22/0.52  fof(f462,plain,(
% 0.22/0.52    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_1),
% 0.22/0.52    inference(superposition,[],[f31,f454])).
% 0.22/0.52  fof(f454,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f37,f33])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.52  fof(f461,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl3_2),
% 0.22/0.52    inference(resolution,[],[f40,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f28,f24])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl3_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f474,plain,(
% 0.22/0.52    spl3_3 | spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f20,f39,f52])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.52  fof(f460,plain,(
% 0.22/0.52    ~spl3_2 | spl3_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f459])).
% 0.22/0.52  fof(f459,plain,(
% 0.22/0.52    $false | (~spl3_2 | spl3_3)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f458])).
% 0.22/0.52  fof(f458,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | (~spl3_2 | spl3_3)),
% 0.22/0.52    inference(superposition,[],[f457,f62])).
% 0.22/0.52  fof(f457,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_2 | spl3_3)),
% 0.22/0.52    inference(forward_demodulation,[],[f456,f437])).
% 0.22/0.52  fof(f437,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.22/0.52    inference(forward_demodulation,[],[f429,f60])).
% 0.22/0.52  fof(f429,plain,(
% 0.22/0.52    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f382,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f80,f26])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.22/0.52    inference(superposition,[],[f29,f62])).
% 0.22/0.52  fof(f382,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X2)) ) | ~spl3_2),
% 0.22/0.52    inference(forward_demodulation,[],[f369,f304])).
% 0.22/0.52  fof(f304,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f29,f287])).
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.52    inference(forward_demodulation,[],[f262,f60])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f31,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f33,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f39])).
% 0.22/0.52  fof(f369,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X2))) ) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f304,f26])).
% 0.22/0.52  fof(f456,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_3),
% 0.22/0.52    inference(resolution,[],[f54,f32])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f52])).
% 0.22/0.52  fof(f453,plain,(
% 0.22/0.52    spl3_1 | ~spl3_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f452])).
% 0.22/0.52  fof(f452,plain,(
% 0.22/0.52    $false | (spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f451])).
% 0.22/0.52  fof(f451,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(superposition,[],[f447,f62])).
% 0.22/0.52  fof(f447,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(backward_demodulation,[],[f66,f438])).
% 0.22/0.52  fof(f438,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 0.22/0.52    inference(forward_demodulation,[],[f430,f60])).
% 0.22/0.52  fof(f430,plain,(
% 0.22/0.52    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_2),
% 0.22/0.52    inference(superposition,[],[f382,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 0.22/0.52    inference(superposition,[],[f86,f23])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_1),
% 0.22/0.52    inference(resolution,[],[f32,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f35])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~spl3_2 | ~spl3_1 | ~spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f15,f52,f35,f39])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    spl3_1 | spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f19,f39,f35])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (3166)------------------------------
% 0.22/0.52  % (3166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3166)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (3166)Memory used [KB]: 6396
% 0.22/0.52  % (3166)Time elapsed: 0.104 s
% 0.22/0.52  % (3166)------------------------------
% 0.22/0.52  % (3166)------------------------------
% 0.22/0.53  % (3163)Success in time 0.166 s
%------------------------------------------------------------------------------

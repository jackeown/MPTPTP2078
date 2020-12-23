%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 263 expanded)
%              Number of leaves         :   13 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  183 ( 504 expanded)
%              Number of equality atoms :   54 ( 219 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f460,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f48,f406,f413,f426,f459])).

fof(f459,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f457])).

fof(f457,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f450,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f30,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f450,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f439,f432])).

fof(f432,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f428,f22])).

fof(f428,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f427])).

fof(f427,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f33])).

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

fof(f46,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f439,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | spl3_2 ),
    inference(backward_demodulation,[],[f414,f424])).

fof(f424,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_1 ),
    inference(superposition,[],[f29,f419])).

fof(f419,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f415,f22])).

fof(f415,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f31,f407])).

fof(f407,plain,
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

fof(f414,plain,
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

fof(f426,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39,f45])).

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

fof(f413,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2
    | spl3_3 ),
    inference(superposition,[],[f410,f43])).

fof(f410,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(forward_demodulation,[],[f409,f390])).

fof(f390,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f382,f22])).

fof(f382,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f358,f80])).

fof(f80,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f74,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f74,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f29,f43])).

fof(f358,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f349,f324])).

fof(f324,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_2 ),
    inference(superposition,[],[f29,f309])).

fof(f309,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f285,f22])).

fof(f285,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f31,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f349,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X2))
    | ~ spl3_2 ),
    inference(superposition,[],[f324,f25])).

fof(f409,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_3 ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f406,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f404])).

fof(f404,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f400,f43])).

fof(f400,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f60,f391])).

fof(f391,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f383,f22])).

fof(f383,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f358,f84])).

fof(f84,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f80,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f60,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f32,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f48,plain,
    ( ~ spl3_2
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f45,f35,f39])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (28020)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (28024)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (28023)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (28020)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (28035)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (28028)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (28027)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (28031)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (28032)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (28033)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (28018)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (28022)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (28025)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f460,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f42,f48,f406,f413,f426,f459])).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f458])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f457])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(superposition,[],[f450,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f30,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f21,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f439,f432])).
% 0.21/0.50  fof(f432,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.21/0.50    inference(forward_demodulation,[],[f428,f22])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.21/0.50    inference(superposition,[],[f31,f427])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f46,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f27,f24])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    r1_xboole_0(sK0,sK2) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f24])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_1 | spl3_2)),
% 0.21/0.50    inference(backward_demodulation,[],[f414,f424])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_1),
% 0.21/0.50    inference(superposition,[],[f29,f419])).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.50    inference(forward_demodulation,[],[f415,f22])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_1),
% 0.21/0.50    inference(superposition,[],[f31,f407])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f37,f33])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl3_2),
% 0.21/0.50    inference(resolution,[],[f40,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f28,f24])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl3_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    spl3_3 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f39,f45])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    ~spl3_2 | spl3_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f412])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    $false | (~spl3_2 | spl3_3)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f411])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | (~spl3_2 | spl3_3)),
% 0.21/0.50    inference(superposition,[],[f410,f43])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_2 | spl3_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f409,f390])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.50    inference(forward_demodulation,[],[f382,f22])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.50    inference(superposition,[],[f358,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f74,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.21/0.50    inference(superposition,[],[f29,f43])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X2)) ) | ~spl3_2),
% 0.21/0.50    inference(forward_demodulation,[],[f349,f324])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_2),
% 0.21/0.50    inference(superposition,[],[f29,f309])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.21/0.50    inference(forward_demodulation,[],[f285,f22])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_2),
% 0.21/0.50    inference(superposition,[],[f31,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f33,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f39])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(X2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X2))) ) | ~spl3_2),
% 0.21/0.50    inference(superposition,[],[f324,f25])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_3),
% 0.21/0.50    inference(resolution,[],[f47,f32])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    spl3_1 | ~spl3_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f405])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    $false | (spl3_1 | ~spl3_2)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f404])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_2)),
% 0.21/0.50    inference(superposition,[],[f400,f43])).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_1 | ~spl3_2)),
% 0.21/0.50    inference(backward_demodulation,[],[f60,f391])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 0.21/0.50    inference(forward_demodulation,[],[f383,f22])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_2),
% 0.21/0.50    inference(superposition,[],[f358,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X2))) )),
% 0.21/0.50    inference(superposition,[],[f80,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_1),
% 0.21/0.50    inference(resolution,[],[f32,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f35])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~spl3_2 | ~spl3_1 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f45,f35,f39])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl3_1 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f39,f35])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28020)------------------------------
% 0.21/0.50  % (28020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28020)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28020)Memory used [KB]: 6268
% 0.21/0.50  % (28020)Time elapsed: 0.063 s
% 0.21/0.50  % (28020)------------------------------
% 0.21/0.50  % (28020)------------------------------
% 0.21/0.50  % (28017)Success in time 0.137 s
%------------------------------------------------------------------------------

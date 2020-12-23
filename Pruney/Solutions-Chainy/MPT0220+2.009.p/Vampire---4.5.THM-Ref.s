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
% DateTime   : Thu Dec  3 12:35:37 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 310 expanded)
%              Number of leaves         :   18 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  109 ( 434 expanded)
%              Number of equality atoms :   66 ( 310 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f854,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f230,f849,f853])).

fof(f853,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f850])).

fof(f850,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f54,f848])).

fof(f848,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f846])).

fof(f846,plain,
    ( spl2_4
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f50,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f849,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f839,f227,f846])).

fof(f227,plain,
    ( spl2_3
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f839,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_3 ),
    inference(trivial_inequality_removal,[],[f838])).

fof(f838,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_3 ),
    inference(forward_demodulation,[],[f804,f256])).

fof(f256,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1 ),
    inference(superposition,[],[f224,f37])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f224,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X5)) = X5 ),
    inference(forward_demodulation,[],[f219,f79])).

fof(f79,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f78,f37])).

fof(f78,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(global_subsumption,[],[f58,f77])).

fof(f77,plain,(
    ! [X1] :
      ( k5_xboole_0(X1,k1_xboole_0) = X1
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f53,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f219,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X5)) = k5_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f35,f153])).

fof(f153,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f52,f53])).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f30,f36,f47])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f804,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_3 ),
    inference(superposition,[],[f229,f489])).

fof(f489,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X5,X6) = k3_xboole_0(X5,X5)
      | ~ r1_tarski(X5,X6) ) ),
    inference(forward_demodulation,[],[f488,f79])).

fof(f488,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X5,X6) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X5,X5))
      | ~ r1_tarski(X5,X6) ) ),
    inference(forward_demodulation,[],[f463,f37])).

fof(f463,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X5,X6) = k5_xboole_0(k3_xboole_0(X5,X5),k1_xboole_0)
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f366,f55])).

fof(f366,plain,(
    ! [X4,X3] : k5_xboole_0(k3_xboole_0(X3,X3),k5_xboole_0(X3,X4)) = X4 ),
    inference(superposition,[],[f224,f275])).

fof(f275,plain,(
    ! [X4] : k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4)) = X4 ),
    inference(forward_demodulation,[],[f258,f78])).

fof(f258,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4)) ),
    inference(superposition,[],[f224,f153])).

fof(f229,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f227])).

fof(f230,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f211,f227])).

fof(f211,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f51,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f28,f49,f47,f50,f49])).

fof(f28,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:20:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (3449)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (3440)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (3440)Refutation not found, incomplete strategy% (3440)------------------------------
% 0.21/0.51  % (3440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  % (3430)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (3440)Memory used [KB]: 1663
% 0.21/0.51  % (3440)Time elapsed: 0.053 s
% 0.21/0.51  % (3440)------------------------------
% 0.21/0.51  % (3440)------------------------------
% 0.21/0.52  % (3432)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.53  % (3438)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.53  % (3438)Refutation not found, incomplete strategy% (3438)------------------------------
% 1.30/0.53  % (3438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (3438)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (3438)Memory used [KB]: 10618
% 1.30/0.53  % (3438)Time elapsed: 0.107 s
% 1.30/0.53  % (3438)------------------------------
% 1.30/0.53  % (3438)------------------------------
% 1.30/0.54  % (3455)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.54  % (3447)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.54  % (3455)Refutation not found, incomplete strategy% (3455)------------------------------
% 1.30/0.54  % (3455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (3429)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (3426)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (3455)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (3455)Memory used [KB]: 10618
% 1.30/0.54  % (3455)Time elapsed: 0.117 s
% 1.30/0.54  % (3455)------------------------------
% 1.30/0.54  % (3455)------------------------------
% 1.30/0.54  % (3427)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.54  % (3427)Refutation not found, incomplete strategy% (3427)------------------------------
% 1.30/0.54  % (3427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (3427)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (3427)Memory used [KB]: 1663
% 1.30/0.54  % (3427)Time elapsed: 0.125 s
% 1.30/0.54  % (3427)------------------------------
% 1.30/0.54  % (3427)------------------------------
% 1.30/0.54  % (3452)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.54  % (3452)Refutation not found, incomplete strategy% (3452)------------------------------
% 1.30/0.54  % (3452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (3452)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (3452)Memory used [KB]: 6140
% 1.30/0.54  % (3452)Time elapsed: 0.137 s
% 1.30/0.54  % (3452)------------------------------
% 1.30/0.54  % (3452)------------------------------
% 1.30/0.54  % (3434)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.54  % (3433)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.54  % (3428)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.41/0.54  % (3454)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.54  % (3454)Refutation not found, incomplete strategy% (3454)------------------------------
% 1.41/0.54  % (3454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (3454)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (3454)Memory used [KB]: 6140
% 1.41/0.54  % (3454)Time elapsed: 0.140 s
% 1.41/0.54  % (3454)------------------------------
% 1.41/0.54  % (3454)------------------------------
% 1.41/0.55  % (3446)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.55  % (3445)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (3445)Refutation not found, incomplete strategy% (3445)------------------------------
% 1.41/0.55  % (3445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3445)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3445)Memory used [KB]: 1663
% 1.41/0.55  % (3445)Time elapsed: 0.139 s
% 1.41/0.55  % (3445)------------------------------
% 1.41/0.55  % (3445)------------------------------
% 1.41/0.55  % (3431)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.41/0.55  % (3436)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.55  % (3451)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.55  % (3435)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (3437)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.55  % (3450)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.55  % (3436)Refutation not found, incomplete strategy% (3436)------------------------------
% 1.41/0.55  % (3436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3436)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3436)Memory used [KB]: 10618
% 1.41/0.55  % (3436)Time elapsed: 0.149 s
% 1.41/0.55  % (3436)------------------------------
% 1.41/0.55  % (3436)------------------------------
% 1.41/0.55  % (3437)Refutation not found, incomplete strategy% (3437)------------------------------
% 1.41/0.55  % (3437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3437)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3437)Memory used [KB]: 6140
% 1.41/0.55  % (3437)Time elapsed: 0.152 s
% 1.41/0.55  % (3437)------------------------------
% 1.41/0.55  % (3437)------------------------------
% 1.41/0.55  % (3451)Refutation not found, incomplete strategy% (3451)------------------------------
% 1.41/0.55  % (3451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (3451)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (3451)Memory used [KB]: 10618
% 1.41/0.55  % (3451)Time elapsed: 0.147 s
% 1.41/0.55  % (3451)------------------------------
% 1.41/0.55  % (3451)------------------------------
% 1.41/0.55  % (3453)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.56  % (3453)Refutation not found, incomplete strategy% (3453)------------------------------
% 1.41/0.56  % (3453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (3453)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (3453)Memory used [KB]: 6140
% 1.41/0.56  % (3453)Time elapsed: 0.147 s
% 1.41/0.56  % (3453)------------------------------
% 1.41/0.56  % (3453)------------------------------
% 1.41/0.56  % (3444)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.56  % (3444)Refutation not found, incomplete strategy% (3444)------------------------------
% 1.41/0.56  % (3444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (3443)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.56  % (3444)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (3444)Memory used [KB]: 1663
% 1.41/0.56  % (3444)Time elapsed: 0.147 s
% 1.41/0.56  % (3444)------------------------------
% 1.41/0.56  % (3444)------------------------------
% 1.41/0.56  % (3456)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.56  % (3443)Refutation not found, incomplete strategy% (3443)------------------------------
% 1.41/0.56  % (3443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (3443)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (3443)Memory used [KB]: 10618
% 1.41/0.56  % (3443)Time elapsed: 0.147 s
% 1.41/0.56  % (3443)------------------------------
% 1.41/0.56  % (3443)------------------------------
% 1.41/0.56  % (3456)Refutation not found, incomplete strategy% (3456)------------------------------
% 1.41/0.56  % (3456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (3456)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (3456)Memory used [KB]: 1663
% 1.41/0.56  % (3456)Time elapsed: 0.146 s
% 1.41/0.56  % (3456)------------------------------
% 1.41/0.56  % (3456)------------------------------
% 1.41/0.56  % (3441)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.56  % (3439)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.57  % (3448)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.61  % (3450)Refutation found. Thanks to Tanya!
% 1.41/0.61  % SZS status Theorem for theBenchmark
% 1.41/0.61  % SZS output start Proof for theBenchmark
% 1.41/0.61  fof(f854,plain,(
% 1.41/0.61    $false),
% 1.41/0.61    inference(avatar_sat_refutation,[],[f230,f849,f853])).
% 1.41/0.61  fof(f853,plain,(
% 1.41/0.61    spl2_4),
% 1.41/0.61    inference(avatar_contradiction_clause,[],[f850])).
% 1.41/0.61  fof(f850,plain,(
% 1.41/0.61    $false | spl2_4),
% 1.41/0.61    inference(unit_resulting_resolution,[],[f54,f848])).
% 1.41/0.61  fof(f848,plain,(
% 1.41/0.61    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_4),
% 1.41/0.61    inference(avatar_component_clause,[],[f846])).
% 1.41/0.61  fof(f846,plain,(
% 1.41/0.61    spl2_4 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.41/0.61  fof(f54,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.41/0.61    inference(definition_unfolding,[],[f32,f50,f49])).
% 1.41/0.61  fof(f49,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f34,f48])).
% 1.41/0.61  fof(f48,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f44,f46])).
% 1.41/0.61  fof(f46,plain,(
% 1.41/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f14])).
% 1.41/0.61  fof(f14,axiom,(
% 1.41/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.41/0.61  fof(f44,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f13])).
% 1.41/0.61  fof(f13,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.61  fof(f34,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f12])).
% 1.41/0.61  fof(f12,axiom,(
% 1.41/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.61  fof(f50,plain,(
% 1.41/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f33,f49])).
% 1.41/0.61  fof(f33,plain,(
% 1.41/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f11])).
% 1.41/0.61  fof(f11,axiom,(
% 1.41/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.61  fof(f32,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f18])).
% 1.41/0.61  fof(f18,axiom,(
% 1.41/0.61    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.41/0.61  fof(f849,plain,(
% 1.41/0.61    ~spl2_4 | spl2_3),
% 1.41/0.61    inference(avatar_split_clause,[],[f839,f227,f846])).
% 1.41/0.61  fof(f227,plain,(
% 1.41/0.61    spl2_3 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 1.41/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.41/0.61  fof(f839,plain,(
% 1.41/0.61    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_3),
% 1.41/0.61    inference(trivial_inequality_removal,[],[f838])).
% 1.41/0.61  fof(f838,plain,(
% 1.41/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_3),
% 1.41/0.61    inference(forward_demodulation,[],[f804,f256])).
% 1.41/0.61  fof(f256,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1) )),
% 1.41/0.61    inference(superposition,[],[f224,f37])).
% 1.41/0.61  fof(f37,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f2])).
% 1.41/0.61  fof(f2,axiom,(
% 1.41/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.41/0.61  fof(f224,plain,(
% 1.41/0.61    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X5)) = X5) )),
% 1.41/0.61    inference(forward_demodulation,[],[f219,f79])).
% 1.41/0.61  fof(f79,plain,(
% 1.41/0.61    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.41/0.61    inference(superposition,[],[f78,f37])).
% 1.41/0.61  fof(f78,plain,(
% 1.41/0.61    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.41/0.61    inference(global_subsumption,[],[f58,f77])).
% 1.41/0.61  fof(f77,plain,(
% 1.41/0.61    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1 | ~r1_tarski(X1,X1)) )),
% 1.41/0.61    inference(superposition,[],[f53,f55])).
% 1.41/0.61  fof(f55,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.61    inference(definition_unfolding,[],[f39,f36])).
% 1.41/0.61  fof(f36,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f6])).
% 1.41/0.61  fof(f6,axiom,(
% 1.41/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.41/0.61  fof(f39,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f25])).
% 1.41/0.61  fof(f25,plain,(
% 1.41/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.41/0.61    inference(nnf_transformation,[],[f5])).
% 1.41/0.61  fof(f5,axiom,(
% 1.41/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.41/0.61  fof(f53,plain,(
% 1.41/0.61    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 1.41/0.61    inference(definition_unfolding,[],[f31,f47])).
% 1.41/0.61  fof(f47,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.41/0.61    inference(definition_unfolding,[],[f29,f36])).
% 1.41/0.61  fof(f29,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f10])).
% 1.41/0.61  fof(f10,axiom,(
% 1.41/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.41/0.61  fof(f31,plain,(
% 1.41/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.41/0.61    inference(cnf_transformation,[],[f21])).
% 1.41/0.61  fof(f21,plain,(
% 1.41/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.41/0.61    inference(rectify,[],[f3])).
% 1.41/0.61  fof(f3,axiom,(
% 1.41/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.41/0.61  fof(f58,plain,(
% 1.41/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.61    inference(equality_resolution,[],[f42])).
% 1.41/0.61  fof(f42,plain,(
% 1.41/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.61    inference(cnf_transformation,[],[f27])).
% 1.41/0.61  fof(f27,plain,(
% 1.41/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.61    inference(flattening,[],[f26])).
% 1.41/0.61  fof(f26,plain,(
% 1.41/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.61    inference(nnf_transformation,[],[f4])).
% 1.41/0.61  fof(f4,axiom,(
% 1.41/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.61  fof(f219,plain,(
% 1.41/0.61    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X5)) = k5_xboole_0(k1_xboole_0,X5)) )),
% 1.41/0.61    inference(superposition,[],[f35,f153])).
% 1.41/0.61  fof(f153,plain,(
% 1.41/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.41/0.61    inference(superposition,[],[f52,f53])).
% 1.41/0.61  fof(f52,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.41/0.61    inference(definition_unfolding,[],[f30,f36,f47])).
% 1.41/0.61  fof(f30,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f8])).
% 1.41/0.61  fof(f8,axiom,(
% 1.41/0.61    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.41/0.61  fof(f35,plain,(
% 1.41/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.41/0.61    inference(cnf_transformation,[],[f9])).
% 1.41/0.61  fof(f9,axiom,(
% 1.41/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.41/0.61  fof(f804,plain,(
% 1.41/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_3),
% 1.41/0.61    inference(superposition,[],[f229,f489])).
% 1.41/0.61  fof(f489,plain,(
% 1.41/0.61    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(X5,X5) | ~r1_tarski(X5,X6)) )),
% 1.41/0.61    inference(forward_demodulation,[],[f488,f79])).
% 1.41/0.61  fof(f488,plain,(
% 1.41/0.61    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X5,X5)) | ~r1_tarski(X5,X6)) )),
% 1.41/0.61    inference(forward_demodulation,[],[f463,f37])).
% 1.41/0.61  fof(f463,plain,(
% 1.41/0.61    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(k3_xboole_0(X5,X5),k1_xboole_0) | ~r1_tarski(X5,X6)) )),
% 1.41/0.61    inference(superposition,[],[f366,f55])).
% 1.41/0.61  fof(f366,plain,(
% 1.41/0.61    ( ! [X4,X3] : (k5_xboole_0(k3_xboole_0(X3,X3),k5_xboole_0(X3,X4)) = X4) )),
% 1.41/0.61    inference(superposition,[],[f224,f275])).
% 1.41/0.61  fof(f275,plain,(
% 1.41/0.61    ( ! [X4] : (k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4)) = X4) )),
% 1.41/0.61    inference(forward_demodulation,[],[f258,f78])).
% 1.41/0.61  fof(f258,plain,(
% 1.41/0.61    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4))) )),
% 1.41/0.61    inference(superposition,[],[f224,f153])).
% 1.41/0.61  fof(f229,plain,(
% 1.41/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | spl2_3),
% 1.41/0.61    inference(avatar_component_clause,[],[f227])).
% 1.41/0.61  fof(f230,plain,(
% 1.41/0.61    ~spl2_3),
% 1.41/0.61    inference(avatar_split_clause,[],[f211,f227])).
% 1.41/0.61  fof(f211,plain,(
% 1.41/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 1.41/0.61    inference(forward_demodulation,[],[f51,f45])).
% 1.41/0.61  fof(f45,plain,(
% 1.41/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.41/0.61    inference(cnf_transformation,[],[f1])).
% 1.41/0.61  fof(f1,axiom,(
% 1.41/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.41/0.61  fof(f51,plain,(
% 1.41/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.41/0.61    inference(definition_unfolding,[],[f28,f49,f47,f50,f49])).
% 1.41/0.61  fof(f28,plain,(
% 1.41/0.61    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.41/0.61    inference(cnf_transformation,[],[f24])).
% 1.41/0.61  fof(f24,plain,(
% 1.41/0.61    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.41/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.41/0.61  fof(f23,plain,(
% 1.41/0.61    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.41/0.61    introduced(choice_axiom,[])).
% 1.41/0.61  fof(f22,plain,(
% 1.41/0.61    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.41/0.61    inference(ennf_transformation,[],[f20])).
% 1.41/0.61  fof(f20,negated_conjecture,(
% 1.41/0.61    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.41/0.61    inference(negated_conjecture,[],[f19])).
% 1.41/0.61  fof(f19,conjecture,(
% 1.41/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.41/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.41/0.61  % SZS output end Proof for theBenchmark
% 1.41/0.61  % (3450)------------------------------
% 1.41/0.61  % (3450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.61  % (3450)Termination reason: Refutation
% 1.41/0.61  
% 1.41/0.61  % (3450)Memory used [KB]: 11257
% 1.41/0.61  % (3450)Time elapsed: 0.185 s
% 1.41/0.61  % (3450)------------------------------
% 1.41/0.61  % (3450)------------------------------
% 1.90/0.63  % (3425)Success in time 0.265 s
%------------------------------------------------------------------------------

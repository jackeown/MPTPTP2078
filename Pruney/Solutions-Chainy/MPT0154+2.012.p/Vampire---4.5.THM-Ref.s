%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:32 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 123 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   74 ( 140 expanded)
%              Number of equality atoms :   54 ( 118 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f74,f2434])).

fof(f2434,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f2433])).

fof(f2433,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f2413])).

fof(f2413,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f67,f324])).

fof(f324,plain,
    ( ! [X2,X3] : k2_tarski(X2,X3) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f323,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f29,f30,f25,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f323,plain,
    ( ! [X2,X3] : k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X3,X3),k2_tarski(X2,X2)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f322,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f322,plain,
    ( ! [X2,X3] : k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2))) = k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2)))))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f314,f202])).

fof(f202,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl4_2 ),
    inference(superposition,[],[f152,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f152,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl4_2 ),
    inference(superposition,[],[f90,f52])).

fof(f90,plain,
    ( ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))
    | ~ spl4_2 ),
    inference(superposition,[],[f38,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_2
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f314,plain,(
    ! [X2,X3] : k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2))) = k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2)))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2)))))) ),
    inference(superposition,[],[f274,f104])).

fof(f104,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f56,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f27,f27])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f274,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(forward_demodulation,[],[f58,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f50,f30])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f45,f30,f25,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f37,f30,f25])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(definition_unfolding,[],[f47,f50,f30,f49,f25])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f67,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_1
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f74,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f69,f71])).

fof(f69,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f55,f23])).

fof(f68,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f65])).

fof(f54,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f22,f49])).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (3958)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.46  % (3969)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.46  % (3962)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.47  % (3962)Refutation not found, incomplete strategy% (3962)------------------------------
% 0.21/0.47  % (3962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3962)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (3962)Memory used [KB]: 10618
% 0.21/0.47  % (3962)Time elapsed: 0.064 s
% 0.21/0.47  % (3962)------------------------------
% 0.21/0.47  % (3962)------------------------------
% 0.21/0.49  % (3982)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (3973)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (3973)Refutation not found, incomplete strategy% (3973)------------------------------
% 0.21/0.49  % (3973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3973)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3973)Memory used [KB]: 10746
% 0.21/0.49  % (3973)Time elapsed: 0.104 s
% 0.21/0.49  % (3973)------------------------------
% 0.21/0.49  % (3973)------------------------------
% 0.21/0.50  % (3966)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (3957)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3957)Refutation not found, incomplete strategy% (3957)------------------------------
% 0.21/0.51  % (3957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3957)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3957)Memory used [KB]: 6140
% 0.21/0.51  % (3957)Time elapsed: 0.099 s
% 0.21/0.51  % (3957)------------------------------
% 0.21/0.51  % (3957)------------------------------
% 0.21/0.51  % (3967)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (3956)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (3954)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (3974)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (3974)Refutation not found, incomplete strategy% (3974)------------------------------
% 0.21/0.51  % (3974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3974)Memory used [KB]: 1663
% 0.21/0.51  % (3974)Time elapsed: 0.082 s
% 0.21/0.51  % (3974)------------------------------
% 0.21/0.51  % (3974)------------------------------
% 0.21/0.52  % (3955)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (3955)Refutation not found, incomplete strategy% (3955)------------------------------
% 0.21/0.52  % (3955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3955)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3955)Memory used [KB]: 10618
% 0.21/0.52  % (3955)Time elapsed: 0.107 s
% 0.21/0.52  % (3955)------------------------------
% 0.21/0.52  % (3955)------------------------------
% 0.21/0.52  % (3972)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (3976)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3959)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (3965)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (3953)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (3953)Refutation not found, incomplete strategy% (3953)------------------------------
% 0.21/0.53  % (3953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3953)Memory used [KB]: 1663
% 0.21/0.53  % (3953)Time elapsed: 0.116 s
% 0.21/0.53  % (3953)------------------------------
% 0.21/0.53  % (3953)------------------------------
% 0.21/0.53  % (3963)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (3963)Refutation not found, incomplete strategy% (3963)------------------------------
% 0.21/0.53  % (3963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3963)Memory used [KB]: 10618
% 0.21/0.53  % (3963)Time elapsed: 0.123 s
% 0.21/0.53  % (3963)------------------------------
% 0.21/0.53  % (3963)------------------------------
% 0.21/0.53  % (3964)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (3977)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (3981)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (3978)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (3978)Refutation not found, incomplete strategy% (3978)------------------------------
% 0.21/0.53  % (3978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3978)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3978)Memory used [KB]: 6268
% 0.21/0.53  % (3978)Time elapsed: 0.130 s
% 0.21/0.53  % (3978)------------------------------
% 0.21/0.53  % (3978)------------------------------
% 0.21/0.54  % (3960)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3968)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (3980)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (3970)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3975)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (3970)Refutation not found, incomplete strategy% (3970)------------------------------
% 0.21/0.54  % (3970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3970)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3970)Memory used [KB]: 10618
% 0.21/0.54  % (3970)Time elapsed: 0.142 s
% 0.21/0.54  % (3970)------------------------------
% 0.21/0.54  % (3970)------------------------------
% 0.21/0.54  % (3975)Refutation not found, incomplete strategy% (3975)------------------------------
% 0.21/0.54  % (3975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3975)Memory used [KB]: 10618
% 0.21/0.54  % (3975)Time elapsed: 0.125 s
% 0.21/0.54  % (3975)------------------------------
% 0.21/0.54  % (3975)------------------------------
% 0.21/0.55  % (3961)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (3979)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (3961)Refutation not found, incomplete strategy% (3961)------------------------------
% 0.21/0.55  % (3961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3961)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3961)Memory used [KB]: 10618
% 0.21/0.55  % (3961)Time elapsed: 0.143 s
% 0.21/0.55  % (3961)------------------------------
% 0.21/0.55  % (3961)------------------------------
% 0.21/0.55  % (3971)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3976)Refutation not found, incomplete strategy% (3976)------------------------------
% 0.21/0.55  % (3976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3976)Memory used [KB]: 1663
% 0.21/0.55  % (3976)Time elapsed: 0.139 s
% 0.21/0.55  % (3976)------------------------------
% 0.21/0.55  % (3976)------------------------------
% 0.21/0.55  % (3964)Refutation not found, incomplete strategy% (3964)------------------------------
% 0.21/0.55  % (3964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3964)Memory used [KB]: 10618
% 0.21/0.55  % (3964)Time elapsed: 0.152 s
% 0.21/0.55  % (3964)------------------------------
% 0.21/0.55  % (3964)------------------------------
% 1.71/0.59  % (3983)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.71/0.59  % (3983)Refutation not found, incomplete strategy% (3983)------------------------------
% 1.71/0.59  % (3983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (3983)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (3983)Memory used [KB]: 6140
% 1.71/0.59  % (3983)Time elapsed: 0.005 s
% 1.71/0.59  % (3983)------------------------------
% 1.71/0.59  % (3983)------------------------------
% 1.71/0.59  % (3969)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.59  % SZS output start Proof for theBenchmark
% 1.71/0.59  fof(f2440,plain,(
% 1.71/0.59    $false),
% 1.71/0.59    inference(avatar_sat_refutation,[],[f68,f74,f2434])).
% 1.71/0.59  fof(f2434,plain,(
% 1.71/0.59    spl4_1 | ~spl4_2),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f2433])).
% 1.71/0.59  fof(f2433,plain,(
% 1.71/0.59    $false | (spl4_1 | ~spl4_2)),
% 1.71/0.59    inference(trivial_inequality_removal,[],[f2413])).
% 1.71/0.59  fof(f2413,plain,(
% 1.71/0.59    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | (spl4_1 | ~spl4_2)),
% 1.71/0.59    inference(superposition,[],[f67,f324])).
% 1.71/0.59  fof(f324,plain,(
% 1.71/0.59    ( ! [X2,X3] : (k2_tarski(X2,X3) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2)))) ) | ~spl4_2),
% 1.71/0.59    inference(forward_demodulation,[],[f323,f53])).
% 1.71/0.59  fof(f53,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f29,f30,f25,f25])).
% 1.71/0.59  fof(f25,plain,(
% 1.71/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f17])).
% 1.71/0.59  fof(f17,axiom,(
% 1.71/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.71/0.59  fof(f30,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f10])).
% 1.71/0.59  fof(f10,axiom,(
% 1.71/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.71/0.59  fof(f29,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f12])).
% 1.71/0.59  fof(f12,axiom,(
% 1.71/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.71/0.59  fof(f323,plain,(
% 1.71/0.59    ( ! [X2,X3] : (k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X3,X3),k2_tarski(X2,X2)))) ) | ~spl4_2),
% 1.71/0.59    inference(forward_demodulation,[],[f322,f55])).
% 1.71/0.59  fof(f55,plain,(
% 1.71/0.59    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.71/0.59    inference(definition_unfolding,[],[f24,f30])).
% 1.71/0.59  fof(f24,plain,(
% 1.71/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f6])).
% 1.71/0.59  fof(f6,axiom,(
% 1.71/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.71/0.59  fof(f322,plain,(
% 1.71/0.59    ( ! [X2,X3] : (k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2))) = k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2)))))) ) | ~spl4_2),
% 1.71/0.59    inference(forward_demodulation,[],[f314,f202])).
% 1.71/0.59  fof(f202,plain,(
% 1.71/0.59    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl4_2),
% 1.71/0.59    inference(superposition,[],[f152,f52])).
% 1.71/0.59  fof(f52,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f28,f27])).
% 1.71/0.59  fof(f27,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f8])).
% 1.71/0.59  fof(f8,axiom,(
% 1.71/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.71/0.59  fof(f28,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f5])).
% 1.71/0.59  fof(f5,axiom,(
% 1.71/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.71/0.59  fof(f152,plain,(
% 1.71/0.59    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl4_2),
% 1.71/0.59    inference(superposition,[],[f90,f52])).
% 1.71/0.59  fof(f90,plain,(
% 1.71/0.59    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) ) | ~spl4_2),
% 1.71/0.59    inference(superposition,[],[f38,f73])).
% 1.71/0.59  fof(f73,plain,(
% 1.71/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_2),
% 1.71/0.59    inference(avatar_component_clause,[],[f71])).
% 1.71/0.59  fof(f71,plain,(
% 1.71/0.59    spl4_2 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.59  fof(f38,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f9])).
% 1.71/0.59  fof(f9,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.71/0.59  fof(f314,plain,(
% 1.71/0.59    ( ! [X2,X3] : (k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X2,X2))) = k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2)))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_tarski(X2,X2))))))) )),
% 1.71/0.59    inference(superposition,[],[f274,f104])).
% 1.71/0.59  fof(f104,plain,(
% 1.71/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.71/0.59    inference(superposition,[],[f56,f23])).
% 1.71/0.59  fof(f23,plain,(
% 1.71/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f7])).
% 1.71/0.59  fof(f7,axiom,(
% 1.71/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.71/0.59  fof(f56,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f26,f27,f27])).
% 1.71/0.59  fof(f26,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f1])).
% 1.71/0.59  fof(f1,axiom,(
% 1.71/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.71/0.59  fof(f274,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 1.71/0.59    inference(forward_demodulation,[],[f58,f57])).
% 1.71/0.59  fof(f57,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f46,f50,f30])).
% 1.71/0.59  fof(f50,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0)))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f45,f30,f25,f49])).
% 1.71/0.59  fof(f49,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f37,f30,f25])).
% 1.71/0.59  fof(f37,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f13])).
% 1.71/0.59  fof(f13,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 1.71/0.59  fof(f45,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f14])).
% 1.71/0.59  fof(f14,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 1.71/0.59  fof(f46,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f11])).
% 1.71/0.59  fof(f11,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 1.71/0.59  fof(f58,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 1.71/0.59    inference(definition_unfolding,[],[f47,f50,f30,f49,f25])).
% 1.71/0.59  fof(f47,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f15])).
% 1.71/0.59  fof(f15,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.71/0.59  fof(f67,plain,(
% 1.71/0.59    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) | spl4_1),
% 1.71/0.59    inference(avatar_component_clause,[],[f65])).
% 1.71/0.59  fof(f65,plain,(
% 1.71/0.59    spl4_1 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.59  fof(f74,plain,(
% 1.71/0.59    spl4_2),
% 1.71/0.59    inference(avatar_split_clause,[],[f69,f71])).
% 1.71/0.59  fof(f69,plain,(
% 1.71/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.71/0.59    inference(superposition,[],[f55,f23])).
% 1.71/0.59  fof(f68,plain,(
% 1.71/0.59    ~spl4_1),
% 1.71/0.59    inference(avatar_split_clause,[],[f54,f65])).
% 1.71/0.59  fof(f54,plain,(
% 1.71/0.59    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.71/0.59    inference(definition_unfolding,[],[f22,f49])).
% 1.71/0.59  fof(f22,plain,(
% 1.71/0.59    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f20])).
% 1.71/0.59  fof(f20,plain,(
% 1.71/0.59    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 1.71/0.59    inference(ennf_transformation,[],[f19])).
% 1.71/0.59  fof(f19,negated_conjecture,(
% 1.71/0.59    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.71/0.59    inference(negated_conjecture,[],[f18])).
% 1.71/0.59  fof(f18,conjecture,(
% 1.71/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.71/0.59  % SZS output end Proof for theBenchmark
% 1.71/0.59  % (3969)------------------------------
% 1.71/0.59  % (3969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (3969)Termination reason: Refutation
% 1.71/0.59  
% 1.71/0.59  % (3969)Memory used [KB]: 12665
% 1.71/0.59  % (3969)Time elapsed: 0.181 s
% 1.71/0.59  % (3969)------------------------------
% 1.71/0.59  % (3969)------------------------------
% 1.71/0.60  % (3952)Success in time 0.231 s
%------------------------------------------------------------------------------

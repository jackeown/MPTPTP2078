%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:11 EST 2020

% Result     : Theorem 5.66s
% Output     : Refutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 226 expanded)
%              Number of leaves         :   15 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :   76 ( 233 expanded)
%              Number of equality atoms :   75 ( 232 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5112,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5038,f106])).

fof(f106,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f91,f62])).

fof(f62,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f35,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f42,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f5038,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f50,f4944])).

fof(f4944,plain,(
    ! [X41,X42] : k4_xboole_0(X41,k4_xboole_0(X41,X42)) = k5_xboole_0(X41,k4_xboole_0(X41,X42)) ),
    inference(forward_demodulation,[],[f4893,f35])).

fof(f4893,plain,(
    ! [X41,X42] : k4_xboole_0(X41,k4_xboole_0(X41,X42)) = k5_xboole_0(k4_xboole_0(X41,X42),X41) ),
    inference(superposition,[],[f106,f1615])).

fof(f1615,plain,(
    ! [X33,X34] : k5_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X34))) = X33 ),
    inference(trivial_inequality_removal,[],[f1610])).

fof(f1610,plain,(
    ! [X33,X34] :
      ( k1_xboole_0 != k1_xboole_0
      | k5_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X34))) = X33 ) ),
    inference(superposition,[],[f1110,f530])).

fof(f530,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X5),X6) ),
    inference(backward_demodulation,[],[f294,f529])).

fof(f529,plain,(
    ! [X17,X18] : k4_xboole_0(X18,X17) = k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17) ),
    inference(forward_demodulation,[],[f528,f310])).

fof(f310,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f282,f31])).

fof(f282,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f57,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f51,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f57,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f528,plain,(
    ! [X17,X18] : k4_xboole_0(k4_xboole_0(X18,X17),X17) = k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17) ),
    inference(forward_demodulation,[],[f514,f35])).

fof(f514,plain,(
    ! [X17,X18] : k4_xboole_0(k4_xboole_0(X18,X17),X17) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X18,X17),X17),X17) ),
    inference(superposition,[],[f55,f482])).

fof(f482,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4 ),
    inference(forward_demodulation,[],[f464,f32])).

fof(f464,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f54,f355])).

fof(f355,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f345,f61])).

fof(f345,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f53,f310])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f37,f37])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f294,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5),X6) ),
    inference(superposition,[],[f57,f61])).

fof(f1110,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(backward_demodulation,[],[f239,f1109])).

fof(f1109,plain,(
    ! [X17,X18] : k1_xboole_0 = k4_xboole_0(X18,k5_xboole_0(X17,k4_xboole_0(X18,X17))) ),
    inference(forward_demodulation,[],[f1108,f61])).

fof(f1108,plain,(
    ! [X17,X18] : k4_xboole_0(X18,X18) = k4_xboole_0(X18,k5_xboole_0(X17,k4_xboole_0(X18,X17))) ),
    inference(forward_demodulation,[],[f1069,f486])).

fof(f486,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X7 ),
    inference(backward_demodulation,[],[f259,f482])).

fof(f259,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,X6),X7)) ),
    inference(forward_demodulation,[],[f242,f57])).

fof(f242,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k4_xboole_0(X7,X6)))) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f53,f55])).

fof(f1069,plain,(
    ! [X17,X18] : k4_xboole_0(X18,k5_xboole_0(X17,k4_xboole_0(X18,X17))) = k4_xboole_0(X18,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),k4_xboole_0(X17,X18))) ),
    inference(superposition,[],[f192,f55])).

fof(f192,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f54,f53])).

fof(f239,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(superposition,[],[f40,f55])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f50,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f28,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26440)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (26443)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (26439)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (26461)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (26453)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (26441)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (26461)Refutation not found, incomplete strategy% (26461)------------------------------
% 0.20/0.51  % (26461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26461)Memory used [KB]: 6140
% 0.20/0.51  % (26461)Time elapsed: 0.074 s
% 0.20/0.51  % (26461)------------------------------
% 0.20/0.51  % (26461)------------------------------
% 0.20/0.51  % (26442)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (26445)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (26456)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (26453)Refutation not found, incomplete strategy% (26453)------------------------------
% 0.20/0.51  % (26453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26453)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26453)Memory used [KB]: 1663
% 0.20/0.51  % (26453)Time elapsed: 0.075 s
% 0.20/0.51  % (26453)------------------------------
% 0.20/0.51  % (26453)------------------------------
% 0.20/0.51  % (26445)Refutation not found, incomplete strategy% (26445)------------------------------
% 0.20/0.51  % (26445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26438)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (26444)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (26437)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (26459)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (26459)Refutation not found, incomplete strategy% (26459)------------------------------
% 0.20/0.52  % (26459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26455)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (26435)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (26460)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (26436)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (26436)Refutation not found, incomplete strategy% (26436)------------------------------
% 0.20/0.52  % (26436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26436)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26436)Memory used [KB]: 1663
% 0.20/0.52  % (26436)Time elapsed: 0.116 s
% 0.20/0.52  % (26436)------------------------------
% 0.20/0.52  % (26436)------------------------------
% 0.20/0.52  % (26447)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (26448)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (26446)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (26458)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (26462)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (26457)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (26454)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (26445)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26445)Memory used [KB]: 10618
% 0.20/0.53  % (26445)Time elapsed: 0.107 s
% 0.20/0.53  % (26445)------------------------------
% 0.20/0.53  % (26445)------------------------------
% 0.20/0.53  % (26464)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (26451)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (26449)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (26449)Refutation not found, incomplete strategy% (26449)------------------------------
% 0.20/0.53  % (26449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26449)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26449)Memory used [KB]: 1663
% 0.20/0.53  % (26449)Time elapsed: 0.132 s
% 0.20/0.53  % (26449)------------------------------
% 0.20/0.53  % (26449)------------------------------
% 0.20/0.53  % (26450)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (26451)Refutation not found, incomplete strategy% (26451)------------------------------
% 0.20/0.53  % (26451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26451)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26451)Memory used [KB]: 10618
% 0.20/0.53  % (26451)Time elapsed: 0.126 s
% 0.20/0.53  % (26451)------------------------------
% 0.20/0.53  % (26451)------------------------------
% 0.20/0.54  % (26459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26459)Memory used [KB]: 10618
% 0.20/0.54  % (26459)Time elapsed: 0.122 s
% 0.20/0.54  % (26459)------------------------------
% 0.20/0.54  % (26459)------------------------------
% 0.20/0.54  % (26463)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (26447)Refutation not found, incomplete strategy% (26447)------------------------------
% 0.20/0.54  % (26447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26447)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26447)Memory used [KB]: 10618
% 0.20/0.54  % (26447)Time elapsed: 0.142 s
% 0.20/0.54  % (26447)------------------------------
% 0.20/0.54  % (26447)------------------------------
% 0.20/0.54  % (26463)Refutation not found, incomplete strategy% (26463)------------------------------
% 0.20/0.54  % (26463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26462)Refutation not found, incomplete strategy% (26462)------------------------------
% 0.20/0.54  % (26462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26462)Memory used [KB]: 6140
% 0.20/0.54  % (26462)Time elapsed: 0.142 s
% 0.20/0.54  % (26462)------------------------------
% 0.20/0.54  % (26462)------------------------------
% 1.42/0.55  % (26452)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.55  % (26463)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (26463)Memory used [KB]: 10618
% 1.42/0.55  % (26463)Time elapsed: 0.145 s
% 1.42/0.55  % (26463)------------------------------
% 1.42/0.55  % (26463)------------------------------
% 1.42/0.56  % (26452)Refutation not found, incomplete strategy% (26452)------------------------------
% 1.42/0.56  % (26452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (26452)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (26452)Memory used [KB]: 1663
% 1.58/0.56  % (26452)Time elapsed: 0.162 s
% 1.58/0.56  % (26452)------------------------------
% 1.58/0.56  % (26452)------------------------------
% 1.58/0.62  % (26474)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.96/0.63  % (26474)Refutation not found, incomplete strategy% (26474)------------------------------
% 1.96/0.63  % (26474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.63  % (26474)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.63  
% 1.96/0.63  % (26474)Memory used [KB]: 10618
% 1.96/0.63  % (26474)Time elapsed: 0.042 s
% 1.96/0.63  % (26474)------------------------------
% 1.96/0.63  % (26474)------------------------------
% 1.96/0.63  % (26475)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.96/0.64  % (26475)Refutation not found, incomplete strategy% (26475)------------------------------
% 1.96/0.64  % (26475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.64  % (26475)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.64  
% 1.96/0.64  % (26475)Memory used [KB]: 1663
% 1.96/0.64  % (26475)Time elapsed: 0.047 s
% 1.96/0.64  % (26475)------------------------------
% 1.96/0.64  % (26475)------------------------------
% 1.96/0.64  % (26468)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.96/0.64  % (26476)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.96/0.65  % (26469)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.96/0.65  % (26438)Refutation not found, incomplete strategy% (26438)------------------------------
% 1.96/0.65  % (26438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.65  % (26438)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.65  
% 1.96/0.65  % (26438)Memory used [KB]: 6140
% 1.96/0.65  % (26438)Time elapsed: 0.247 s
% 1.96/0.65  % (26438)------------------------------
% 1.96/0.65  % (26438)------------------------------
% 1.96/0.66  % (26472)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.29/0.66  % (26450)Refutation not found, incomplete strategy% (26450)------------------------------
% 2.29/0.66  % (26450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.66  % (26450)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.66  
% 2.29/0.66  % (26450)Memory used [KB]: 6140
% 2.29/0.66  % (26450)Time elapsed: 0.252 s
% 2.29/0.66  % (26450)------------------------------
% 2.29/0.66  % (26450)------------------------------
% 2.29/0.67  % (26477)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.29/0.68  % (26478)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.29/0.69  % (26473)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.29/0.69  % (26480)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.29/0.69  % (26479)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.29/0.69  % (26479)Refutation not found, incomplete strategy% (26479)------------------------------
% 2.29/0.69  % (26479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.69  % (26479)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.69  
% 2.29/0.69  % (26479)Memory used [KB]: 10618
% 2.29/0.69  % (26479)Time elapsed: 0.118 s
% 2.29/0.69  % (26479)------------------------------
% 2.29/0.69  % (26479)------------------------------
% 2.72/0.74  % (26487)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.72/0.74  % (26489)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.91/0.78  % (26492)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.91/0.78  % (26492)Refutation not found, incomplete strategy% (26492)------------------------------
% 2.91/0.78  % (26492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.78  % (26492)Termination reason: Refutation not found, incomplete strategy
% 2.91/0.78  
% 2.91/0.78  % (26492)Memory used [KB]: 10618
% 2.91/0.78  % (26492)Time elapsed: 0.104 s
% 2.91/0.78  % (26492)------------------------------
% 2.91/0.78  % (26492)------------------------------
% 2.91/0.81  % (26437)Time limit reached!
% 2.91/0.81  % (26437)------------------------------
% 2.91/0.81  % (26437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.81  % (26437)Termination reason: Time limit
% 2.91/0.81  
% 2.91/0.81  % (26437)Memory used [KB]: 6652
% 2.91/0.81  % (26437)Time elapsed: 0.407 s
% 2.91/0.81  % (26437)------------------------------
% 2.91/0.81  % (26437)------------------------------
% 2.91/0.81  % (26507)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.25/0.83  % (26512)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.40/0.91  % (26549)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.40/0.91  % (26441)Time limit reached!
% 3.40/0.91  % (26441)------------------------------
% 3.40/0.91  % (26441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.91  % (26441)Termination reason: Time limit
% 3.40/0.91  
% 3.40/0.91  % (26441)Memory used [KB]: 15991
% 3.40/0.91  % (26441)Time elapsed: 0.510 s
% 3.40/0.91  % (26441)------------------------------
% 3.40/0.91  % (26441)------------------------------
% 3.77/0.94  % (26569)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.77/0.95  % (26507)Refutation not found, incomplete strategy% (26507)------------------------------
% 3.77/0.95  % (26507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.95  % (26507)Termination reason: Refutation not found, incomplete strategy
% 3.77/0.95  
% 3.77/0.95  % (26507)Memory used [KB]: 6140
% 3.77/0.95  % (26507)Time elapsed: 0.251 s
% 3.77/0.95  % (26507)------------------------------
% 3.77/0.95  % (26507)------------------------------
% 4.01/1.02  % (26442)Time limit reached!
% 4.01/1.02  % (26442)------------------------------
% 4.01/1.02  % (26442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/1.03  % (26442)Termination reason: Time limit
% 4.01/1.03  
% 4.01/1.03  % (26442)Memory used [KB]: 6268
% 4.01/1.03  % (26442)Time elapsed: 0.618 s
% 4.01/1.03  % (26442)------------------------------
% 4.01/1.03  % (26442)------------------------------
% 4.35/1.05  % (26464)Time limit reached!
% 4.35/1.05  % (26464)------------------------------
% 4.35/1.05  % (26464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/1.05  % (26631)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 4.35/1.06  % (26464)Termination reason: Time limit
% 4.35/1.06  
% 4.35/1.06  % (26464)Memory used [KB]: 55521
% 4.35/1.06  % (26464)Time elapsed: 0.611 s
% 4.35/1.06  % (26464)------------------------------
% 4.35/1.06  % (26464)------------------------------
% 5.66/1.08  % (26646)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 5.66/1.08  % (26646)Refutation not found, incomplete strategy% (26646)------------------------------
% 5.66/1.08  % (26646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.66/1.08  % (26646)Termination reason: Refutation not found, incomplete strategy
% 5.66/1.08  
% 5.66/1.08  % (26646)Memory used [KB]: 1663
% 5.66/1.08  % (26646)Time elapsed: 0.106 s
% 5.66/1.08  % (26646)------------------------------
% 5.66/1.08  % (26646)------------------------------
% 5.66/1.09  % (26457)Refutation found. Thanks to Tanya!
% 5.66/1.09  % SZS status Theorem for theBenchmark
% 5.66/1.09  % SZS output start Proof for theBenchmark
% 5.66/1.09  fof(f5112,plain,(
% 5.66/1.09    $false),
% 5.66/1.09    inference(subsumption_resolution,[],[f5038,f106])).
% 5.66/1.09  fof(f106,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.66/1.09    inference(forward_demodulation,[],[f91,f62])).
% 5.66/1.09  fof(f62,plain,(
% 5.66/1.09    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.66/1.09    inference(superposition,[],[f35,f31])).
% 5.66/1.09  fof(f31,plain,(
% 5.66/1.09    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.66/1.09    inference(cnf_transformation,[],[f13])).
% 5.66/1.09  fof(f13,axiom,(
% 5.66/1.09    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 5.66/1.09  fof(f35,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.66/1.09    inference(cnf_transformation,[],[f2])).
% 5.66/1.09  fof(f2,axiom,(
% 5.66/1.09    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.66/1.09  fof(f91,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.66/1.09    inference(superposition,[],[f42,f30])).
% 5.66/1.09  fof(f30,plain,(
% 5.66/1.09    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.66/1.09    inference(cnf_transformation,[],[f15])).
% 5.66/1.09  fof(f15,axiom,(
% 5.66/1.09    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.66/1.09  fof(f42,plain,(
% 5.66/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.66/1.09    inference(cnf_transformation,[],[f14])).
% 5.66/1.09  fof(f14,axiom,(
% 5.66/1.09    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.66/1.09  fof(f5038,plain,(
% 5.66/1.09    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 5.66/1.09    inference(backward_demodulation,[],[f50,f4944])).
% 5.66/1.09  fof(f4944,plain,(
% 5.66/1.09    ( ! [X41,X42] : (k4_xboole_0(X41,k4_xboole_0(X41,X42)) = k5_xboole_0(X41,k4_xboole_0(X41,X42))) )),
% 5.66/1.09    inference(forward_demodulation,[],[f4893,f35])).
% 5.66/1.09  fof(f4893,plain,(
% 5.66/1.09    ( ! [X41,X42] : (k4_xboole_0(X41,k4_xboole_0(X41,X42)) = k5_xboole_0(k4_xboole_0(X41,X42),X41)) )),
% 5.66/1.09    inference(superposition,[],[f106,f1615])).
% 5.66/1.09  fof(f1615,plain,(
% 5.66/1.09    ( ! [X33,X34] : (k5_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X34))) = X33) )),
% 5.66/1.09    inference(trivial_inequality_removal,[],[f1610])).
% 5.66/1.09  fof(f1610,plain,(
% 5.66/1.09    ( ! [X33,X34] : (k1_xboole_0 != k1_xboole_0 | k5_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X34))) = X33) )),
% 5.66/1.09    inference(superposition,[],[f1110,f530])).
% 5.66/1.09  fof(f530,plain,(
% 5.66/1.09    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X5),X6)) )),
% 5.66/1.09    inference(backward_demodulation,[],[f294,f529])).
% 5.66/1.09  fof(f529,plain,(
% 5.66/1.09    ( ! [X17,X18] : (k4_xboole_0(X18,X17) = k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17)) )),
% 5.66/1.09    inference(forward_demodulation,[],[f528,f310])).
% 5.66/1.09  fof(f310,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 5.66/1.09    inference(forward_demodulation,[],[f282,f31])).
% 5.66/1.09  fof(f282,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) )),
% 5.66/1.09    inference(superposition,[],[f57,f61])).
% 5.66/1.09  fof(f61,plain,(
% 5.66/1.09    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.66/1.09    inference(backward_demodulation,[],[f51,f32])).
% 5.66/1.09  fof(f32,plain,(
% 5.66/1.09    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.66/1.09    inference(cnf_transformation,[],[f6])).
% 5.66/1.09  fof(f6,axiom,(
% 5.66/1.09    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.66/1.09  fof(f51,plain,(
% 5.66/1.09    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 5.66/1.09    inference(definition_unfolding,[],[f29,f37])).
% 5.66/1.09  fof(f37,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.66/1.09    inference(cnf_transformation,[],[f11])).
% 5.66/1.09  fof(f11,axiom,(
% 5.66/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.66/1.09  fof(f29,plain,(
% 5.66/1.09    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.66/1.09    inference(cnf_transformation,[],[f4])).
% 5.66/1.09  fof(f4,axiom,(
% 5.66/1.09    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 5.66/1.09  fof(f57,plain,(
% 5.66/1.09    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 5.66/1.09    inference(definition_unfolding,[],[f43,f36])).
% 5.66/1.09  fof(f36,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.66/1.09    inference(cnf_transformation,[],[f16])).
% 5.66/1.09  fof(f16,axiom,(
% 5.66/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.66/1.09  fof(f43,plain,(
% 5.66/1.09    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.66/1.09    inference(cnf_transformation,[],[f8])).
% 5.66/1.09  fof(f8,axiom,(
% 5.66/1.09    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.66/1.09  fof(f528,plain,(
% 5.66/1.09    ( ! [X17,X18] : (k4_xboole_0(k4_xboole_0(X18,X17),X17) = k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17)) )),
% 5.66/1.09    inference(forward_demodulation,[],[f514,f35])).
% 5.66/1.09  fof(f514,plain,(
% 5.66/1.09    ( ! [X17,X18] : (k4_xboole_0(k4_xboole_0(X18,X17),X17) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X18,X17),X17),X17)) )),
% 5.66/1.09    inference(superposition,[],[f55,f482])).
% 5.66/1.09  fof(f482,plain,(
% 5.66/1.09    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) )),
% 5.66/1.09    inference(forward_demodulation,[],[f464,f32])).
% 5.66/1.09  fof(f464,plain,(
% 5.66/1.09    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4))) )),
% 5.66/1.09    inference(superposition,[],[f54,f355])).
% 5.66/1.09  fof(f355,plain,(
% 5.66/1.09    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,X7)))) )),
% 5.66/1.09    inference(forward_demodulation,[],[f345,f61])).
% 5.66/1.09  fof(f345,plain,(
% 5.66/1.09    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 5.66/1.09    inference(superposition,[],[f53,f310])).
% 5.66/1.09  fof(f53,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 5.66/1.09    inference(definition_unfolding,[],[f34,f37,f37])).
% 5.66/1.09  fof(f34,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.66/1.09    inference(cnf_transformation,[],[f1])).
% 5.66/1.09  fof(f1,axiom,(
% 5.66/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.66/1.09  fof(f54,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 5.66/1.09    inference(definition_unfolding,[],[f38,f37])).
% 5.66/1.09  fof(f38,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.66/1.09    inference(cnf_transformation,[],[f10])).
% 5.66/1.09  fof(f10,axiom,(
% 5.66/1.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.66/1.09  fof(f55,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 5.66/1.09    inference(definition_unfolding,[],[f39,f36])).
% 5.66/1.09  fof(f39,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 5.66/1.09    inference(cnf_transformation,[],[f7])).
% 5.66/1.09  fof(f7,axiom,(
% 5.66/1.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 5.66/1.09  fof(f294,plain,(
% 5.66/1.09    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5),X6)) )),
% 5.66/1.09    inference(superposition,[],[f57,f61])).
% 5.66/1.09  fof(f1110,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 5.66/1.09    inference(backward_demodulation,[],[f239,f1109])).
% 5.66/1.09  fof(f1109,plain,(
% 5.66/1.09    ( ! [X17,X18] : (k1_xboole_0 = k4_xboole_0(X18,k5_xboole_0(X17,k4_xboole_0(X18,X17)))) )),
% 5.66/1.09    inference(forward_demodulation,[],[f1108,f61])).
% 5.66/1.09  fof(f1108,plain,(
% 5.66/1.09    ( ! [X17,X18] : (k4_xboole_0(X18,X18) = k4_xboole_0(X18,k5_xboole_0(X17,k4_xboole_0(X18,X17)))) )),
% 5.66/1.09    inference(forward_demodulation,[],[f1069,f486])).
% 5.66/1.09  fof(f486,plain,(
% 5.66/1.09    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X7) )),
% 5.66/1.09    inference(backward_demodulation,[],[f259,f482])).
% 5.66/1.09  fof(f259,plain,(
% 5.66/1.09    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k4_xboole_0(k4_xboole_0(X7,X6),X7))) )),
% 5.66/1.09    inference(forward_demodulation,[],[f242,f57])).
% 5.66/1.09  fof(f242,plain,(
% 5.66/1.09    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k4_xboole_0(X7,X6)))) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7))) )),
% 5.66/1.09    inference(superposition,[],[f53,f55])).
% 5.66/1.09  fof(f1069,plain,(
% 5.66/1.09    ( ! [X17,X18] : (k4_xboole_0(X18,k5_xboole_0(X17,k4_xboole_0(X18,X17))) = k4_xboole_0(X18,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),k4_xboole_0(X17,X18)))) )),
% 5.66/1.09    inference(superposition,[],[f192,f55])).
% 5.66/1.09  fof(f192,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 5.66/1.09    inference(superposition,[],[f54,f53])).
% 5.66/1.09  fof(f239,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 5.66/1.09    inference(superposition,[],[f40,f55])).
% 5.66/1.09  fof(f40,plain,(
% 5.66/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 5.66/1.09    inference(cnf_transformation,[],[f20])).
% 5.66/1.09  fof(f20,plain,(
% 5.66/1.09    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 5.66/1.09    inference(ennf_transformation,[],[f5])).
% 5.66/1.09  fof(f5,axiom,(
% 5.66/1.09    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 5.66/1.09  fof(f50,plain,(
% 5.66/1.09    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 5.66/1.09    inference(definition_unfolding,[],[f28,f37])).
% 5.66/1.09  fof(f28,plain,(
% 5.66/1.09    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.66/1.09    inference(cnf_transformation,[],[f22])).
% 5.66/1.09  fof(f22,plain,(
% 5.66/1.09    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.66/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 5.66/1.09  fof(f21,plain,(
% 5.66/1.09    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.66/1.09    introduced(choice_axiom,[])).
% 5.66/1.09  fof(f19,plain,(
% 5.66/1.09    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.66/1.09    inference(ennf_transformation,[],[f18])).
% 5.66/1.09  fof(f18,negated_conjecture,(
% 5.66/1.09    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.66/1.09    inference(negated_conjecture,[],[f17])).
% 5.66/1.09  fof(f17,conjecture,(
% 5.66/1.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.66/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.66/1.09  % SZS output end Proof for theBenchmark
% 5.66/1.09  % (26457)------------------------------
% 5.66/1.09  % (26457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.66/1.09  % (26457)Termination reason: Refutation
% 5.66/1.09  
% 5.66/1.09  % (26457)Memory used [KB]: 11897
% 5.66/1.09  % (26457)Time elapsed: 0.640 s
% 5.66/1.09  % (26457)------------------------------
% 5.66/1.09  % (26457)------------------------------
% 5.66/1.10  % (26432)Success in time 0.751 s
%------------------------------------------------------------------------------

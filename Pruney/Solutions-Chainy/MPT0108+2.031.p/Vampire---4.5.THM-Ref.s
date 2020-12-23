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
% DateTime   : Thu Dec  3 12:32:22 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 134 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :   72 ( 141 expanded)
%              Number of equality atoms :   63 ( 132 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f812,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f811])).

fof(f811,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f810,f101])).

fof(f101,plain,(
    ! [X1] : k5_xboole_0(X1,o_0_0_xboole_0) = X1 ),
    inference(global_subsumption,[],[f81,f93])).

fof(f93,plain,(
    ! [X1] :
      ( k5_xboole_0(X1,o_0_0_xboole_0) = X1
      | ~ r1_xboole_0(X1,o_0_0_xboole_0) ) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] : o_0_0_xboole_0 = k3_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f25,f24,f24])).

fof(f24,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f81,plain,(
    ! [X0] : r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != o_0_0_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f810,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,o_0_0_xboole_0)) ),
    inference(forward_demodulation,[],[f809,f65])).

fof(f65,plain,(
    ! [X1] : o_0_0_xboole_0 = k3_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[],[f30,f45])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f809,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(o_0_0_xboole_0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK0)))) ),
    inference(forward_demodulation,[],[f808,f218])).

fof(f218,plain,(
    ! [X14,X15,X13] : k3_xboole_0(X13,k3_xboole_0(X14,X15)) = k3_xboole_0(X15,k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f40,f30])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f808,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(o_0_0_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(forward_demodulation,[],[f807,f60])).

fof(f60,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f29,f24,f33,f43])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f807,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(forward_demodulation,[],[f806,f30])).

fof(f806,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))) ),
    inference(forward_demodulation,[],[f805,f30])).

fof(f805,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),k5_xboole_0(sK1,sK1))))) ),
    inference(forward_demodulation,[],[f804,f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f804,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))))) ),
    inference(backward_demodulation,[],[f476,f714])).

fof(f714,plain,(
    ! [X12,X13,X11] : k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,X12)),k5_xboole_0(X13,k3_xboole_0(X13,X11))) = k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(X12,k5_xboole_0(X11,k3_xboole_0(X12,X11))))) ),
    inference(superposition,[],[f55,f30])).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f41,f33,f43,f33,f33])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f476,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f475,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f54,f40])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f39,f33,f33])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f475,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f432,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f432,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) ),
    inference(superposition,[],[f61,f38])).

fof(f61,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f59,f40])).

fof(f59,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f58,f30])).

fof(f58,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f44,f30])).

fof(f44,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f23,f33,f43])).

fof(f23,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (17274)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (17266)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (17266)Refutation not found, incomplete strategy% (17266)------------------------------
% 0.20/0.51  % (17266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17266)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17266)Memory used [KB]: 6140
% 0.20/0.51  % (17266)Time elapsed: 0.099 s
% 0.20/0.51  % (17266)------------------------------
% 0.20/0.51  % (17266)------------------------------
% 0.20/0.51  % (17279)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (17279)Refutation not found, incomplete strategy% (17279)------------------------------
% 0.20/0.51  % (17279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17279)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17279)Memory used [KB]: 10618
% 0.20/0.51  % (17279)Time elapsed: 0.110 s
% 0.20/0.51  % (17279)------------------------------
% 0.20/0.51  % (17279)------------------------------
% 0.20/0.51  % (17285)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (17282)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (17290)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (17265)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (17271)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (17271)Refutation not found, incomplete strategy% (17271)------------------------------
% 0.20/0.52  % (17271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17271)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17271)Memory used [KB]: 10618
% 0.20/0.52  % (17271)Time elapsed: 0.111 s
% 0.20/0.52  % (17271)------------------------------
% 0.20/0.52  % (17271)------------------------------
% 0.20/0.52  % (17276)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (17287)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (17282)Refutation not found, incomplete strategy% (17282)------------------------------
% 0.20/0.52  % (17282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17282)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17282)Memory used [KB]: 10618
% 0.20/0.52  % (17282)Time elapsed: 0.105 s
% 0.20/0.52  % (17282)------------------------------
% 0.20/0.52  % (17282)------------------------------
% 1.28/0.52  % (17287)Refutation not found, incomplete strategy% (17287)------------------------------
% 1.28/0.52  % (17287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (17287)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (17287)Memory used [KB]: 6268
% 1.28/0.52  % (17287)Time elapsed: 0.119 s
% 1.28/0.52  % (17287)------------------------------
% 1.28/0.52  % (17287)------------------------------
% 1.28/0.52  % (17277)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.52  % (17277)Refutation not found, incomplete strategy% (17277)------------------------------
% 1.28/0.52  % (17277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (17277)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (17277)Memory used [KB]: 6140
% 1.28/0.52  % (17277)Time elapsed: 0.002 s
% 1.28/0.52  % (17277)------------------------------
% 1.28/0.52  % (17277)------------------------------
% 1.28/0.52  % (17289)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.52  % (17262)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.52  % (17262)Refutation not found, incomplete strategy% (17262)------------------------------
% 1.28/0.52  % (17262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (17262)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (17262)Memory used [KB]: 1663
% 1.28/0.52  % (17262)Time elapsed: 0.114 s
% 1.28/0.52  % (17262)------------------------------
% 1.28/0.52  % (17262)------------------------------
% 1.28/0.53  % (17264)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (17268)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.53  % (17264)Refutation not found, incomplete strategy% (17264)------------------------------
% 1.28/0.53  % (17264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (17264)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (17264)Memory used [KB]: 10618
% 1.28/0.53  % (17264)Time elapsed: 0.115 s
% 1.28/0.53  % (17264)------------------------------
% 1.28/0.53  % (17264)------------------------------
% 1.28/0.53  % (17269)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.53  % (17281)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.53  % (17263)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.53  % (17284)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (17267)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (17286)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.53  % (17284)Refutation not found, incomplete strategy% (17284)------------------------------
% 1.28/0.53  % (17284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (17284)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (17284)Memory used [KB]: 10746
% 1.28/0.53  % (17284)Time elapsed: 0.094 s
% 1.28/0.53  % (17284)------------------------------
% 1.28/0.53  % (17284)------------------------------
% 1.28/0.54  % (17285)Refutation not found, incomplete strategy% (17285)------------------------------
% 1.28/0.54  % (17285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (17285)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (17285)Memory used [KB]: 1791
% 1.28/0.54  % (17285)Time elapsed: 0.089 s
% 1.28/0.54  % (17285)------------------------------
% 1.28/0.54  % (17285)------------------------------
% 1.28/0.54  % (17273)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (17270)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.54  % (17270)Refutation not found, incomplete strategy% (17270)------------------------------
% 1.28/0.54  % (17270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (17270)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (17270)Memory used [KB]: 10618
% 1.28/0.54  % (17270)Time elapsed: 0.131 s
% 1.28/0.54  % (17270)------------------------------
% 1.28/0.54  % (17270)------------------------------
% 1.28/0.54  % (17288)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (17278)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.55  % (17280)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (17283)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.55  % (17283)Refutation not found, incomplete strategy% (17283)------------------------------
% 1.47/0.55  % (17283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (17283)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (17283)Memory used [KB]: 1663
% 1.47/0.55  % (17283)Time elapsed: 0.139 s
% 1.47/0.55  % (17283)------------------------------
% 1.47/0.55  % (17283)------------------------------
% 1.47/0.55  % (17275)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.55  % (17272)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.55  % (17272)Refutation not found, incomplete strategy% (17272)------------------------------
% 1.47/0.55  % (17272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (17272)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (17272)Memory used [KB]: 10618
% 1.47/0.55  % (17272)Time elapsed: 0.149 s
% 1.47/0.55  % (17272)------------------------------
% 1.47/0.55  % (17272)------------------------------
% 1.47/0.55  % (17291)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.47/0.59  % (17286)Refutation found. Thanks to Tanya!
% 1.47/0.59  % SZS status Theorem for theBenchmark
% 1.47/0.59  % SZS output start Proof for theBenchmark
% 1.47/0.59  fof(f812,plain,(
% 1.47/0.59    $false),
% 1.47/0.59    inference(trivial_inequality_removal,[],[f811])).
% 1.47/0.59  fof(f811,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1)),
% 1.47/0.59    inference(forward_demodulation,[],[f810,f101])).
% 1.47/0.59  fof(f101,plain,(
% 1.47/0.59    ( ! [X1] : (k5_xboole_0(X1,o_0_0_xboole_0) = X1) )),
% 1.47/0.59    inference(global_subsumption,[],[f81,f93])).
% 1.47/0.59  fof(f93,plain,(
% 1.47/0.59    ( ! [X1] : (k5_xboole_0(X1,o_0_0_xboole_0) = X1 | ~r1_xboole_0(X1,o_0_0_xboole_0)) )),
% 1.47/0.59    inference(superposition,[],[f50,f45])).
% 1.47/0.59  fof(f45,plain,(
% 1.47/0.59    ( ! [X0] : (o_0_0_xboole_0 = k3_xboole_0(X0,o_0_0_xboole_0)) )),
% 1.47/0.59    inference(definition_unfolding,[],[f25,f24,f24])).
% 1.47/0.59  fof(f24,plain,(
% 1.47/0.59    k1_xboole_0 = o_0_0_xboole_0),
% 1.47/0.59    inference(cnf_transformation,[],[f2])).
% 1.47/0.59  fof(f2,axiom,(
% 1.47/0.59    k1_xboole_0 = o_0_0_xboole_0),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.47/0.59  fof(f25,plain,(
% 1.47/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f8])).
% 1.47/0.59  fof(f8,axiom,(
% 1.47/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.47/0.59  fof(f50,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.59    inference(definition_unfolding,[],[f35,f33])).
% 1.47/0.59  fof(f33,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f5])).
% 1.47/0.59  fof(f5,axiom,(
% 1.47/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.47/0.59  fof(f35,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f14])).
% 1.47/0.59  fof(f14,axiom,(
% 1.47/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.47/0.59  fof(f81,plain,(
% 1.47/0.59    ( ! [X0] : (r1_xboole_0(X0,o_0_0_xboole_0)) )),
% 1.47/0.59    inference(unit_resulting_resolution,[],[f45,f53])).
% 1.47/0.59  fof(f53,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != o_0_0_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.47/0.59    inference(definition_unfolding,[],[f36,f24])).
% 1.47/0.59  fof(f36,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f3])).
% 1.47/0.59  fof(f3,axiom,(
% 1.47/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.47/0.59  fof(f810,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,o_0_0_xboole_0))),
% 1.47/0.59    inference(forward_demodulation,[],[f809,f65])).
% 1.47/0.59  fof(f65,plain,(
% 1.47/0.59    ( ! [X1] : (o_0_0_xboole_0 = k3_xboole_0(o_0_0_xboole_0,X1)) )),
% 1.47/0.59    inference(superposition,[],[f30,f45])).
% 1.47/0.59  fof(f30,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f1])).
% 1.47/0.59  fof(f1,axiom,(
% 1.47/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.47/0.59  fof(f809,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(o_0_0_xboole_0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK0))))),
% 1.47/0.59    inference(forward_demodulation,[],[f808,f218])).
% 1.47/0.59  fof(f218,plain,(
% 1.47/0.59    ( ! [X14,X15,X13] : (k3_xboole_0(X13,k3_xboole_0(X14,X15)) = k3_xboole_0(X15,k3_xboole_0(X13,X14))) )),
% 1.47/0.59    inference(superposition,[],[f40,f30])).
% 1.47/0.59  fof(f40,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f6])).
% 1.47/0.59  fof(f6,axiom,(
% 1.47/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.47/0.59  fof(f808,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(o_0_0_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.47/0.59    inference(forward_demodulation,[],[f807,f60])).
% 1.47/0.59  fof(f60,plain,(
% 1.47/0.59    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.47/0.59    inference(backward_demodulation,[],[f48,f49])).
% 1.47/0.59  fof(f49,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.47/0.59    inference(definition_unfolding,[],[f31,f43])).
% 1.47/0.59  fof(f43,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.47/0.59    inference(definition_unfolding,[],[f32,f33])).
% 1.47/0.59  fof(f32,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f16])).
% 1.47/0.59  fof(f16,axiom,(
% 1.47/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.47/0.59  fof(f31,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.47/0.59    inference(cnf_transformation,[],[f7])).
% 1.47/0.59  fof(f7,axiom,(
% 1.47/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.47/0.59  fof(f48,plain,(
% 1.47/0.59    ( ! [X0,X1] : (o_0_0_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.47/0.59    inference(definition_unfolding,[],[f29,f24,f33,f43])).
% 1.47/0.59  fof(f29,plain,(
% 1.47/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f9])).
% 1.47/0.59  fof(f9,axiom,(
% 1.47/0.59    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.47/0.59  fof(f807,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.47/0.59    inference(forward_demodulation,[],[f806,f30])).
% 1.47/0.59  fof(f806,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))))),
% 1.47/0.59    inference(forward_demodulation,[],[f805,f30])).
% 1.47/0.59  fof(f805,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),k5_xboole_0(sK1,sK1)))))),
% 1.47/0.59    inference(forward_demodulation,[],[f804,f28])).
% 1.47/0.59  fof(f28,plain,(
% 1.47/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.47/0.59    inference(cnf_transformation,[],[f19])).
% 1.47/0.59  fof(f19,plain,(
% 1.47/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.47/0.59    inference(rectify,[],[f4])).
% 1.47/0.59  fof(f4,axiom,(
% 1.47/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.47/0.59  fof(f804,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))))))),
% 1.47/0.59    inference(backward_demodulation,[],[f476,f714])).
% 1.47/0.59  fof(f714,plain,(
% 1.47/0.59    ( ! [X12,X13,X11] : (k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,X12)),k5_xboole_0(X13,k3_xboole_0(X13,X11))) = k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(X12,k5_xboole_0(X11,k3_xboole_0(X12,X11)))))) )),
% 1.47/0.59    inference(superposition,[],[f55,f30])).
% 1.47/0.59  fof(f55,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X2)))) )),
% 1.47/0.59    inference(definition_unfolding,[],[f41,f33,f43,f33,f33])).
% 1.47/0.59  fof(f41,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f11])).
% 1.47/0.59  fof(f11,axiom,(
% 1.47/0.59    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.47/0.59  fof(f476,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 1.47/0.59    inference(forward_demodulation,[],[f475,f62])).
% 1.47/0.59  fof(f62,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 1.47/0.59    inference(backward_demodulation,[],[f54,f40])).
% 1.47/0.59  fof(f54,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.47/0.59    inference(definition_unfolding,[],[f39,f33,f33])).
% 1.47/0.59  fof(f39,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.47/0.59    inference(cnf_transformation,[],[f10])).
% 1.47/0.59  fof(f10,axiom,(
% 1.47/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.47/0.59  fof(f475,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 1.47/0.59    inference(forward_demodulation,[],[f432,f38])).
% 1.47/0.59  fof(f38,plain,(
% 1.47/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.47/0.59    inference(cnf_transformation,[],[f15])).
% 1.47/0.59  fof(f15,axiom,(
% 1.47/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.47/0.59  fof(f432,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))),
% 1.47/0.59    inference(superposition,[],[f61,f38])).
% 1.47/0.59  fof(f61,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.47/0.59    inference(backward_demodulation,[],[f59,f40])).
% 1.47/0.59  fof(f59,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 1.47/0.59    inference(forward_demodulation,[],[f58,f30])).
% 1.47/0.59  fof(f58,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 1.47/0.59    inference(backward_demodulation,[],[f44,f30])).
% 1.47/0.59  fof(f44,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 1.47/0.59    inference(definition_unfolding,[],[f23,f33,f43])).
% 1.47/0.59  fof(f23,plain,(
% 1.47/0.59    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.47/0.59    inference(cnf_transformation,[],[f20])).
% 1.47/0.59  fof(f20,plain,(
% 1.47/0.59    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.47/0.59    inference(ennf_transformation,[],[f18])).
% 1.47/0.59  fof(f18,negated_conjecture,(
% 1.47/0.59    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.47/0.59    inference(negated_conjecture,[],[f17])).
% 1.47/0.59  fof(f17,conjecture,(
% 1.47/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.47/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 1.47/0.59  % SZS output end Proof for theBenchmark
% 1.47/0.59  % (17286)------------------------------
% 1.47/0.59  % (17286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.59  % (17286)Termination reason: Refutation
% 1.47/0.59  
% 1.47/0.59  % (17286)Memory used [KB]: 6780
% 1.47/0.59  % (17286)Time elapsed: 0.168 s
% 1.47/0.59  % (17286)------------------------------
% 1.47/0.59  % (17286)------------------------------
% 1.47/0.59  % (17261)Success in time 0.224 s
%------------------------------------------------------------------------------

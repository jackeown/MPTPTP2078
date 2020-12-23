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
% DateTime   : Thu Dec  3 12:36:38 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 195 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  117 ( 260 expanded)
%              Number of equality atoms :   83 ( 207 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f466,plain,(
    $false ),
    inference(subsumption_resolution,[],[f464,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f88,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X1] : sP6(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP6(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f464,plain,(
    ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f139,f461])).

fof(f461,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f460,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f57,f61,f61])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f460,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f459,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f56,f61,f61])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f459,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f455,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f455,plain,(
    k3_enumset1(sK1,sK1,sK1,sK2,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f65,f433])).

fof(f433,plain,(
    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(forward_demodulation,[],[f430,f342])).

fof(f342,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f110,f340])).

fof(f340,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f215,f339])).

fof(f339,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f331,f46])).

fof(f331,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f111,f222])).

fof(f222,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f219,f46])).

fof(f219,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f64,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f31,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f111,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f64,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f44,f42,f42])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f215,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f105,f72])).

fof(f110,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f64,f73])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f430,plain,(
    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f64,f106])).

fof(f106,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f66,f67])).

fof(f66,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f27,f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f62])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f41,f58,f59,f63])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f139,plain,(
    ~ r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f93,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f62])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f93,plain,(
    ~ sP4(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f29,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:55:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (26193)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.18/0.51  % (26169)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.18/0.51  % (26168)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.18/0.51  % (26167)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.18/0.52  % (26175)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.18/0.52  % (26193)Refutation not found, incomplete strategy% (26193)------------------------------
% 1.18/0.52  % (26193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (26165)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.18/0.53  % (26165)Refutation not found, incomplete strategy% (26165)------------------------------
% 1.18/0.53  % (26165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (26165)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (26165)Memory used [KB]: 1663
% 1.18/0.53  % (26165)Time elapsed: 0.103 s
% 1.18/0.53  % (26165)------------------------------
% 1.18/0.53  % (26165)------------------------------
% 1.18/0.53  % (26172)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.18/0.53  % (26193)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (26193)Memory used [KB]: 6268
% 1.18/0.53  % (26193)Time elapsed: 0.105 s
% 1.18/0.53  % (26193)------------------------------
% 1.18/0.53  % (26193)------------------------------
% 1.29/0.53  % (26166)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.53  % (26175)Refutation not found, incomplete strategy% (26175)------------------------------
% 1.29/0.53  % (26175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (26175)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (26175)Memory used [KB]: 6268
% 1.29/0.53  % (26175)Time elapsed: 0.104 s
% 1.29/0.53  % (26175)------------------------------
% 1.29/0.53  % (26175)------------------------------
% 1.29/0.53  % (26192)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.53  % (26176)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.29/0.53  % (26187)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.53  % (26173)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.53  % (26176)Refutation not found, incomplete strategy% (26176)------------------------------
% 1.29/0.53  % (26176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (26176)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (26176)Memory used [KB]: 10618
% 1.29/0.53  % (26176)Time elapsed: 0.119 s
% 1.29/0.53  % (26176)------------------------------
% 1.29/0.53  % (26176)------------------------------
% 1.29/0.53  % (26178)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.53  % (26192)Refutation not found, incomplete strategy% (26192)------------------------------
% 1.29/0.53  % (26192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (26192)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (26192)Memory used [KB]: 6268
% 1.29/0.53  % (26192)Time elapsed: 0.122 s
% 1.29/0.53  % (26192)------------------------------
% 1.29/0.53  % (26192)------------------------------
% 1.29/0.53  % (26174)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.54  % (26170)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (26180)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.29/0.54  % (26191)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.54  % (26190)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.29/0.54  % (26164)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.29/0.54  % (26182)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.29/0.54  % (26195)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.54  % (26195)Refutation not found, incomplete strategy% (26195)------------------------------
% 1.29/0.54  % (26195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26195)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26195)Memory used [KB]: 1663
% 1.29/0.54  % (26195)Time elapsed: 0.002 s
% 1.29/0.54  % (26195)------------------------------
% 1.29/0.54  % (26195)------------------------------
% 1.29/0.54  % (26184)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.54  % (26181)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.29/0.54  % (26190)Refutation not found, incomplete strategy% (26190)------------------------------
% 1.29/0.54  % (26190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26190)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26190)Memory used [KB]: 10746
% 1.29/0.54  % (26190)Time elapsed: 0.129 s
% 1.29/0.54  % (26190)------------------------------
% 1.29/0.54  % (26190)------------------------------
% 1.29/0.54  % (26194)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.29/0.54  % (26186)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.54  % (26181)Refutation not found, incomplete strategy% (26181)------------------------------
% 1.29/0.54  % (26181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26181)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26181)Memory used [KB]: 1791
% 1.29/0.54  % (26181)Time elapsed: 0.129 s
% 1.29/0.54  % (26181)------------------------------
% 1.29/0.54  % (26181)------------------------------
% 1.29/0.55  % (26171)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.55  % (26185)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.29/0.55  % (26178)Refutation not found, incomplete strategy% (26178)------------------------------
% 1.29/0.55  % (26178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (26178)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (26178)Memory used [KB]: 1791
% 1.29/0.55  % (26178)Time elapsed: 0.124 s
% 1.29/0.55  % (26178)------------------------------
% 1.29/0.55  % (26178)------------------------------
% 1.29/0.56  % (26188)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.29/0.56  % (26182)Refutation not found, incomplete strategy% (26182)------------------------------
% 1.29/0.56  % (26182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (26182)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (26182)Memory used [KB]: 1791
% 1.29/0.56  % (26182)Time elapsed: 0.133 s
% 1.29/0.56  % (26182)------------------------------
% 1.29/0.56  % (26182)------------------------------
% 1.29/0.56  % (26177)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.29/0.56  % (26180)Refutation not found, incomplete strategy% (26180)------------------------------
% 1.29/0.56  % (26180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (26180)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (26180)Memory used [KB]: 10618
% 1.29/0.56  % (26180)Time elapsed: 0.153 s
% 1.29/0.56  % (26180)------------------------------
% 1.29/0.56  % (26180)------------------------------
% 1.29/0.56  % (26179)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.29/0.56  % (26191)Refutation not found, incomplete strategy% (26191)------------------------------
% 1.29/0.56  % (26191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.57  % (26191)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.57  
% 1.29/0.57  % (26191)Memory used [KB]: 6268
% 1.29/0.57  % (26191)Time elapsed: 0.154 s
% 1.29/0.57  % (26191)------------------------------
% 1.29/0.57  % (26191)------------------------------
% 1.29/0.57  % (26184)Refutation found. Thanks to Tanya!
% 1.29/0.57  % SZS status Theorem for theBenchmark
% 1.29/0.58  % SZS output start Proof for theBenchmark
% 1.29/0.58  fof(f466,plain,(
% 1.29/0.58    $false),
% 1.29/0.58    inference(subsumption_resolution,[],[f464,f142])).
% 1.29/0.58  fof(f142,plain,(
% 1.29/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.29/0.58    inference(unit_resulting_resolution,[],[f88,f85])).
% 1.29/0.58  fof(f85,plain,(
% 1.29/0.58    ( ! [X4,X2,X0,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.29/0.58    inference(equality_resolution,[],[f77])).
% 1.29/0.58  fof(f77,plain,(
% 1.29/0.58    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.29/0.58    inference(definition_unfolding,[],[f51,f61])).
% 1.29/0.58  fof(f61,plain,(
% 1.29/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.29/0.58    inference(definition_unfolding,[],[f55,f59])).
% 1.29/0.58  fof(f59,plain,(
% 1.29/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f16])).
% 1.29/0.58  fof(f16,axiom,(
% 1.29/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.29/0.58  fof(f55,plain,(
% 1.29/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f15])).
% 1.29/0.58  fof(f15,axiom,(
% 1.29/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.58  fof(f51,plain,(
% 1.29/0.58    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.29/0.58    inference(cnf_transformation,[],[f26])).
% 1.29/0.58  fof(f26,plain,(
% 1.29/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.29/0.58    inference(ennf_transformation,[],[f9])).
% 1.29/0.58  fof(f9,axiom,(
% 1.29/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.29/0.58  fof(f88,plain,(
% 1.29/0.58    ( ! [X4,X2,X1] : (sP6(X4,X2,X1,X4)) )),
% 1.29/0.58    inference(equality_resolution,[],[f47])).
% 1.29/0.58  fof(f47,plain,(
% 1.29/0.58    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP6(X4,X2,X1,X0)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f26])).
% 1.29/0.58  fof(f464,plain,(
% 1.29/0.58    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK1,sK2))),
% 1.29/0.58    inference(backward_demodulation,[],[f139,f461])).
% 1.29/0.58  fof(f461,plain,(
% 1.29/0.58    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 1.29/0.58    inference(forward_demodulation,[],[f460,f79])).
% 1.29/0.58  fof(f79,plain,(
% 1.29/0.58    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X0,X0,X0,X2,X1)) )),
% 1.29/0.58    inference(definition_unfolding,[],[f57,f61,f61])).
% 1.29/0.58  fof(f57,plain,(
% 1.29/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f20])).
% 1.29/0.58  fof(f20,axiom,(
% 1.29/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 1.29/0.58  fof(f460,plain,(
% 1.29/0.58    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK2,sK1)),
% 1.29/0.58    inference(forward_demodulation,[],[f459,f78])).
% 1.29/0.58  fof(f78,plain,(
% 1.29/0.58    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0)) )),
% 1.29/0.58    inference(definition_unfolding,[],[f56,f61,f61])).
% 1.29/0.58  fof(f56,plain,(
% 1.29/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f11])).
% 1.29/0.58  fof(f11,axiom,(
% 1.29/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 1.29/0.58  fof(f459,plain,(
% 1.29/0.58    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0)),
% 1.29/0.58    inference(forward_demodulation,[],[f455,f46])).
% 1.29/0.58  fof(f46,plain,(
% 1.29/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.58    inference(cnf_transformation,[],[f7])).
% 1.29/0.58  fof(f7,axiom,(
% 1.29/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.29/0.58  fof(f455,plain,(
% 1.29/0.58    k3_enumset1(sK1,sK1,sK1,sK2,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k1_xboole_0)),
% 1.29/0.58    inference(superposition,[],[f65,f433])).
% 1.29/0.58  fof(f433,plain,(
% 1.29/0.58    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.29/0.58    inference(forward_demodulation,[],[f430,f342])).
% 1.29/0.58  fof(f342,plain,(
% 1.29/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.29/0.58    inference(backward_demodulation,[],[f110,f340])).
% 1.29/0.58  fof(f340,plain,(
% 1.29/0.58    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.29/0.58    inference(backward_demodulation,[],[f215,f339])).
% 1.29/0.58  fof(f339,plain,(
% 1.29/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.58    inference(forward_demodulation,[],[f331,f46])).
% 1.29/0.58  fof(f331,plain,(
% 1.29/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.29/0.58    inference(superposition,[],[f111,f222])).
% 1.29/0.58  fof(f222,plain,(
% 1.29/0.58    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.29/0.58    inference(forward_demodulation,[],[f219,f46])).
% 1.29/0.58  fof(f219,plain,(
% 1.29/0.58    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.29/0.58    inference(superposition,[],[f64,f105])).
% 1.29/0.58  fof(f105,plain,(
% 1.29/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.29/0.58    inference(unit_resulting_resolution,[],[f31,f67])).
% 1.29/0.58  fof(f67,plain,(
% 1.29/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.29/0.58    inference(definition_unfolding,[],[f30,f42])).
% 1.29/0.58  fof(f42,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.29/0.58    inference(cnf_transformation,[],[f6])).
% 1.29/0.58  fof(f6,axiom,(
% 1.29/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.29/0.58  fof(f30,plain,(
% 1.29/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.29/0.58    inference(cnf_transformation,[],[f25])).
% 1.29/0.58  fof(f25,plain,(
% 1.29/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.29/0.58    inference(ennf_transformation,[],[f4])).
% 1.29/0.58  fof(f4,axiom,(
% 1.29/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.29/0.58  fof(f31,plain,(
% 1.29/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f5])).
% 1.29/0.58  fof(f5,axiom,(
% 1.29/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.29/0.58  fof(f64,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.29/0.58    inference(definition_unfolding,[],[f43,f42])).
% 1.29/0.58  fof(f43,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.29/0.58    inference(cnf_transformation,[],[f3])).
% 1.29/0.58  fof(f3,axiom,(
% 1.29/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.29/0.58  fof(f111,plain,(
% 1.29/0.58    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 1.29/0.58    inference(superposition,[],[f64,f72])).
% 1.29/0.58  fof(f72,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.29/0.58    inference(definition_unfolding,[],[f44,f42,f42])).
% 1.29/0.58  fof(f44,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f1])).
% 1.29/0.58  fof(f1,axiom,(
% 1.29/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.29/0.58  fof(f215,plain,(
% 1.29/0.58    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.29/0.58    inference(superposition,[],[f105,f72])).
% 1.29/0.58  fof(f110,plain,(
% 1.29/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.29/0.58    inference(superposition,[],[f64,f73])).
% 1.29/0.58  fof(f73,plain,(
% 1.29/0.58    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.29/0.58    inference(definition_unfolding,[],[f45,f42])).
% 1.29/0.58  fof(f45,plain,(
% 1.29/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.29/0.58    inference(cnf_transformation,[],[f23])).
% 1.29/0.58  fof(f23,plain,(
% 1.29/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.29/0.58    inference(rectify,[],[f2])).
% 1.29/0.58  fof(f2,axiom,(
% 1.29/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.29/0.58  fof(f430,plain,(
% 1.29/0.58    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.29/0.58    inference(superposition,[],[f64,f106])).
% 1.29/0.58  fof(f106,plain,(
% 1.29/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 1.29/0.58    inference(unit_resulting_resolution,[],[f66,f67])).
% 1.29/0.58  fof(f66,plain,(
% 1.29/0.58    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.29/0.58    inference(definition_unfolding,[],[f27,f63,f62])).
% 1.29/0.58  fof(f62,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.29/0.58    inference(definition_unfolding,[],[f39,f61])).
% 1.29/0.58  fof(f39,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f14])).
% 1.29/0.58  fof(f14,axiom,(
% 1.29/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.58  fof(f63,plain,(
% 1.29/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.29/0.58    inference(definition_unfolding,[],[f40,f62])).
% 1.29/0.58  fof(f40,plain,(
% 1.29/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.58    inference(cnf_transformation,[],[f13])).
% 1.29/0.58  fof(f13,axiom,(
% 1.29/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.58  fof(f27,plain,(
% 1.29/0.58    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.29/0.58    inference(cnf_transformation,[],[f24])).
% 1.29/0.58  fof(f24,plain,(
% 1.29/0.58    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.29/0.58    inference(ennf_transformation,[],[f22])).
% 1.29/0.58  fof(f22,negated_conjecture,(
% 1.29/0.58    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.29/0.58    inference(negated_conjecture,[],[f21])).
% 1.29/0.58  fof(f21,conjecture,(
% 1.29/0.58    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.29/0.58  fof(f65,plain,(
% 1.29/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) )),
% 1.29/0.58    inference(definition_unfolding,[],[f41,f58,f59,f63])).
% 1.29/0.58  fof(f58,plain,(
% 1.29/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.29/0.58    inference(cnf_transformation,[],[f8])).
% 1.29/0.58  fof(f8,axiom,(
% 1.29/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.29/0.58  fof(f41,plain,(
% 1.29/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.29/0.58    inference(cnf_transformation,[],[f12])).
% 1.29/0.58  fof(f12,axiom,(
% 1.29/0.58    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.29/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 1.29/0.58  fof(f139,plain,(
% 1.29/0.58    ~r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.29/0.58    inference(unit_resulting_resolution,[],[f93,f80])).
% 1.29/0.59  fof(f80,plain,(
% 1.29/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1)) | sP4(X3,X1,X0)) )),
% 1.29/0.59    inference(equality_resolution,[],[f70])).
% 1.29/0.59  fof(f70,plain,(
% 1.29/0.59    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.29/0.59    inference(definition_unfolding,[],[f36,f62])).
% 1.29/0.59  fof(f36,plain,(
% 1.29/0.59    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.29/0.59    inference(cnf_transformation,[],[f10])).
% 1.29/0.59  fof(f10,axiom,(
% 1.29/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.29/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.29/0.59  fof(f93,plain,(
% 1.29/0.59    ~sP4(sK0,sK2,sK1)),
% 1.29/0.59    inference(unit_resulting_resolution,[],[f28,f29,f34])).
% 1.29/0.59  fof(f34,plain,(
% 1.29/0.59    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 1.29/0.59    inference(cnf_transformation,[],[f10])).
% 1.29/0.59  fof(f29,plain,(
% 1.29/0.59    sK0 != sK2),
% 1.29/0.59    inference(cnf_transformation,[],[f24])).
% 1.29/0.59  fof(f28,plain,(
% 1.29/0.59    sK0 != sK1),
% 1.29/0.59    inference(cnf_transformation,[],[f24])).
% 1.29/0.59  % SZS output end Proof for theBenchmark
% 1.29/0.59  % (26184)------------------------------
% 1.29/0.59  % (26184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.59  % (26184)Termination reason: Refutation
% 1.29/0.59  
% 1.29/0.59  % (26184)Memory used [KB]: 1918
% 1.29/0.59  % (26184)Time elapsed: 0.100 s
% 1.29/0.59  % (26184)------------------------------
% 1.29/0.59  % (26184)------------------------------
% 1.29/0.59  % (26157)Success in time 0.219 s
%------------------------------------------------------------------------------

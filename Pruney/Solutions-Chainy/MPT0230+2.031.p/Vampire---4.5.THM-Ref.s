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
% DateTime   : Thu Dec  3 12:36:38 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 160 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 225 expanded)
%              Number of equality atoms :   76 ( 172 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f516,plain,(
    $false ),
    inference(subsumption_resolution,[],[f514,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f86,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f86,plain,(
    ! [X4,X2,X1] : sP6(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP6(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f514,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f137,f511])).

fof(f511,plain,(
    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f510,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f56,f55,f55])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f510,plain,(
    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK1,sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f506,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f506,plain,(
    k2_enumset1(sK1,sK1,sK2,sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f63,f427])).

fof(f427,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(forward_demodulation,[],[f424,f383])).

fof(f383,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f108,f381])).

fof(f381,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f216,f380])).

fof(f380,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f372,f46])).

fof(f372,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f109,f223])).

fof(f223,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f220,f46])).

fof(f220,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f62,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f31,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f109,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f62,f70])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f44,f42,f42])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f216,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f103,f70])).

fof(f108,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f62,f71])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f424,plain,(
    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f62,f104])).

fof(f104,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f64,f65])).

fof(f64,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f27,f61,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f41,f58,f55,f61])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f137,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f91,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f60])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f91,plain,(
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (4995)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (4987)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4990)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (4986)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (4998)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (4982)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (4988)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (4982)Refutation not found, incomplete strategy% (4982)------------------------------
% 0.21/0.53  % (4982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4982)Memory used [KB]: 1663
% 0.21/0.53  % (4982)Time elapsed: 0.083 s
% 0.21/0.53  % (4982)------------------------------
% 0.21/0.53  % (4982)------------------------------
% 0.21/0.53  % (4983)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (4998)Refutation not found, incomplete strategy% (4998)------------------------------
% 0.21/0.53  % (4998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4998)Memory used [KB]: 1791
% 0.21/0.53  % (4998)Time elapsed: 0.096 s
% 0.21/0.53  % (4984)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (4998)------------------------------
% 0.21/0.53  % (4998)------------------------------
% 0.21/0.53  % (4981)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (4999)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (5004)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.54  % (4999)Refutation not found, incomplete strategy% (4999)------------------------------
% 1.34/0.54  % (4999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (4995)Refutation not found, incomplete strategy% (4995)------------------------------
% 1.34/0.54  % (4995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (4995)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (4995)Memory used [KB]: 1791
% 1.34/0.54  % (4995)Time elapsed: 0.125 s
% 1.34/0.54  % (4995)------------------------------
% 1.34/0.54  % (4995)------------------------------
% 1.34/0.54  % (4989)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.54  % (5009)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % (5003)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.54  % (4996)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.54  % (4997)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (5001)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.54  % (5008)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (5010)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (4997)Refutation not found, incomplete strategy% (4997)------------------------------
% 1.34/0.54  % (4997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (5006)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (4985)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.55  % (4997)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (4997)Memory used [KB]: 10618
% 1.34/0.55  % (4997)Time elapsed: 0.126 s
% 1.34/0.55  % (4997)------------------------------
% 1.34/0.55  % (4997)------------------------------
% 1.34/0.55  % (4994)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.55  % (4993)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.55  % (4991)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.55  % (4999)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (4999)Memory used [KB]: 1791
% 1.34/0.55  % (4999)Time elapsed: 0.131 s
% 1.34/0.55  % (4999)------------------------------
% 1.34/0.55  % (4999)------------------------------
% 1.34/0.55  % (5005)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.55  % (5011)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.55  % (4992)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.55  % (5006)Refutation not found, incomplete strategy% (5006)------------------------------
% 1.34/0.55  % (5006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (5006)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (5006)Memory used [KB]: 10746
% 1.34/0.55  % (5006)Time elapsed: 0.133 s
% 1.34/0.55  % (5006)------------------------------
% 1.34/0.55  % (5006)------------------------------
% 1.34/0.55  % (5011)Refutation not found, incomplete strategy% (5011)------------------------------
% 1.34/0.55  % (5011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (5011)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (5011)Memory used [KB]: 1663
% 1.34/0.55  % (5011)Time elapsed: 0.002 s
% 1.34/0.55  % (5011)------------------------------
% 1.34/0.55  % (5011)------------------------------
% 1.34/0.55  % (4992)Refutation not found, incomplete strategy% (4992)------------------------------
% 1.34/0.55  % (4992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (5002)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.53/0.55  % (5008)Refutation not found, incomplete strategy% (5008)------------------------------
% 1.53/0.55  % (5008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (5007)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.53/0.56  % (5009)Refutation not found, incomplete strategy% (5009)------------------------------
% 1.53/0.56  % (5009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (5009)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (5009)Memory used [KB]: 6268
% 1.53/0.56  % (5009)Time elapsed: 0.151 s
% 1.53/0.56  % (5009)------------------------------
% 1.53/0.56  % (5009)------------------------------
% 1.53/0.56  % (4992)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (4992)Memory used [KB]: 6268
% 1.53/0.56  % (4992)Time elapsed: 0.139 s
% 1.53/0.56  % (4992)------------------------------
% 1.53/0.56  % (4992)------------------------------
% 1.53/0.56  % (5007)Refutation not found, incomplete strategy% (5007)------------------------------
% 1.53/0.56  % (5007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (5007)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (5007)Memory used [KB]: 6268
% 1.53/0.56  % (5007)Time elapsed: 0.123 s
% 1.53/0.56  % (5007)------------------------------
% 1.53/0.56  % (5007)------------------------------
% 1.53/0.57  % (5008)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (5008)Memory used [KB]: 6268
% 1.53/0.57  % (5008)Time elapsed: 0.136 s
% 1.53/0.57  % (5008)------------------------------
% 1.53/0.57  % (5008)------------------------------
% 1.53/0.57  % (4993)Refutation not found, incomplete strategy% (4993)------------------------------
% 1.53/0.57  % (4993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (4993)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (4993)Memory used [KB]: 10618
% 1.53/0.57  % (4993)Time elapsed: 0.156 s
% 1.53/0.57  % (4993)------------------------------
% 1.53/0.57  % (4993)------------------------------
% 1.53/0.57  % (5001)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f516,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(subsumption_resolution,[],[f514,f141])).
% 1.53/0.57  fof(f141,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f86,f83])).
% 1.53/0.57  fof(f83,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))) )),
% 1.53/0.57    inference(equality_resolution,[],[f75])).
% 1.53/0.57  fof(f75,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.53/0.57    inference(definition_unfolding,[],[f51,f55])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.53/0.57    inference(cnf_transformation,[],[f26])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.53/0.57    inference(ennf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.53/0.57  fof(f86,plain,(
% 1.53/0.57    ( ! [X4,X2,X1] : (sP6(X4,X2,X1,X4)) )),
% 1.53/0.57    inference(equality_resolution,[],[f47])).
% 1.53/0.57  fof(f47,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP6(X4,X2,X1,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f26])).
% 1.53/0.57  fof(f514,plain,(
% 1.53/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK1,sK2))),
% 1.53/0.57    inference(backward_demodulation,[],[f137,f511])).
% 1.53/0.57  fof(f511,plain,(
% 1.53/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2)),
% 1.53/0.57    inference(forward_demodulation,[],[f510,f76])).
% 1.53/0.57  fof(f76,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f56,f55,f55])).
% 1.53/0.57  fof(f56,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 1.53/0.57  fof(f510,plain,(
% 1.53/0.57    k2_enumset1(sK1,sK1,sK1,sK2) = k2_enumset1(sK1,sK1,sK2,sK0)),
% 1.53/0.57    inference(forward_demodulation,[],[f506,f46])).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.53/0.57  fof(f506,plain,(
% 1.53/0.57    k2_enumset1(sK1,sK1,sK2,sK0) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k1_xboole_0)),
% 1.53/0.57    inference(superposition,[],[f63,f427])).
% 1.53/0.57  fof(f427,plain,(
% 1.53/0.57    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.53/0.57    inference(forward_demodulation,[],[f424,f383])).
% 1.53/0.57  fof(f383,plain,(
% 1.53/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.53/0.57    inference(backward_demodulation,[],[f108,f381])).
% 1.53/0.57  fof(f381,plain,(
% 1.53/0.57    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.53/0.57    inference(backward_demodulation,[],[f216,f380])).
% 1.53/0.57  fof(f380,plain,(
% 1.53/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.57    inference(forward_demodulation,[],[f372,f46])).
% 1.53/0.57  fof(f372,plain,(
% 1.53/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.53/0.57    inference(superposition,[],[f109,f223])).
% 1.53/0.57  fof(f223,plain,(
% 1.53/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.53/0.57    inference(forward_demodulation,[],[f220,f46])).
% 1.53/0.57  fof(f220,plain,(
% 1.53/0.57    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.53/0.57    inference(superposition,[],[f62,f103])).
% 1.53/0.57  fof(f103,plain,(
% 1.53/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f31,f65])).
% 1.53/0.57  fof(f65,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.53/0.57    inference(definition_unfolding,[],[f30,f42])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.57  fof(f31,plain,(
% 1.53/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.53/0.57  fof(f62,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.53/0.57    inference(definition_unfolding,[],[f43,f42])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.57  fof(f109,plain,(
% 1.53/0.57    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 1.53/0.57    inference(superposition,[],[f62,f70])).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.53/0.57    inference(definition_unfolding,[],[f44,f42,f42])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.57  fof(f216,plain,(
% 1.53/0.57    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.53/0.57    inference(superposition,[],[f103,f70])).
% 1.53/0.57  fof(f108,plain,(
% 1.53/0.57    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.53/0.57    inference(superposition,[],[f62,f71])).
% 1.53/0.57  fof(f71,plain,(
% 1.53/0.57    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.53/0.57    inference(definition_unfolding,[],[f45,f42])).
% 1.53/0.57  fof(f45,plain,(
% 1.53/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f23])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.57    inference(rectify,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.53/0.57  fof(f424,plain,(
% 1.53/0.57    k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.53/0.57    inference(superposition,[],[f62,f104])).
% 1.53/0.57  fof(f104,plain,(
% 1.53/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f64,f65])).
% 1.53/0.57  fof(f64,plain,(
% 1.53/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.53/0.57    inference(definition_unfolding,[],[f27,f61,f60])).
% 1.53/0.57  fof(f60,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f39,f55])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f14])).
% 1.53/0.57  fof(f14,axiom,(
% 1.53/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.57  fof(f61,plain,(
% 1.53/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f40,f60])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,axiom,(
% 1.53/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.53/0.57    inference(cnf_transformation,[],[f24])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.53/0.57    inference(ennf_transformation,[],[f22])).
% 1.53/0.57  fof(f22,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.53/0.57    inference(negated_conjecture,[],[f21])).
% 1.53/0.57  fof(f21,conjecture,(
% 1.53/0.57    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.53/0.57  fof(f63,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) )),
% 1.53/0.57    inference(definition_unfolding,[],[f41,f58,f55,f61])).
% 1.53/0.57  fof(f58,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.53/0.58  fof(f137,plain,(
% 1.53/0.58    ~r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f91,f78])).
% 1.53/0.58  fof(f78,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | sP4(X3,X1,X0)) )),
% 1.53/0.58    inference(equality_resolution,[],[f68])).
% 1.53/0.58  fof(f68,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.53/0.58    inference(definition_unfolding,[],[f36,f60])).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.53/0.58    inference(cnf_transformation,[],[f10])).
% 1.53/0.58  fof(f10,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.53/0.58  fof(f91,plain,(
% 1.53/0.58    ~sP4(sK0,sK2,sK1)),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f28,f29,f34])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 1.53/0.58    inference(cnf_transformation,[],[f10])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    sK0 != sK2),
% 1.53/0.58    inference(cnf_transformation,[],[f24])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    sK0 != sK1),
% 1.53/0.58    inference(cnf_transformation,[],[f24])).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (5001)------------------------------
% 1.53/0.58  % (5001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (5001)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (5001)Memory used [KB]: 1918
% 1.53/0.58  % (5001)Time elapsed: 0.164 s
% 1.53/0.58  % (5001)------------------------------
% 1.53/0.58  % (5001)------------------------------
% 1.53/0.58  % (4980)Success in time 0.205 s
%------------------------------------------------------------------------------

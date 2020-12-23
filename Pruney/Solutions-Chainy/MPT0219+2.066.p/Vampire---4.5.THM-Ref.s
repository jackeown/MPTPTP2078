%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:29 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 603 expanded)
%              Number of leaves         :   13 ( 208 expanded)
%              Depth                    :   17
%              Number of atoms          :   80 ( 641 expanded)
%              Number of equality atoms :   68 ( 629 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f25])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f171,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f133,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f133,plain,(
    r2_hidden(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f74,f113])).

fof(f113,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f105,f86])).

fof(f86,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k4_enumset1(sK0,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f83,f56])).

fof(f56,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f24,f53,f53,f53])).

fof(f24,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X0] : k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(X0,X0,X0,X0,X0,X0)) = k4_enumset1(sK0,sK1,sK1,sK1,sK1,X0) ),
    inference(forward_demodulation,[],[f82,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5)) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X4,X5,X6)) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)) ),
    inference(definition_unfolding,[],[f32,f48,f48])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f82,plain,(
    ! [X0] : k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,X0)) = k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(superposition,[],[f61,f56])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)),k4_enumset1(X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8)) ),
    inference(definition_unfolding,[],[f34,f54,f47,f48])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)),k4_enumset1(X8,X8,X8,X8,X8,X8)) ),
    inference(definition_unfolding,[],[f26,f49,f53])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f105,plain,(
    ! [X0] : k4_enumset1(sK0,sK1,sK1,sK1,sK1,X0) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0) ),
    inference(backward_demodulation,[],[f83,f104])).

fof(f104,plain,(
    ! [X2,X1] : k4_enumset1(sK0,X1,X1,X1,X1,X2) = k2_xboole_0(k4_enumset1(sK0,sK0,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)) ),
    inference(forward_demodulation,[],[f100,f55])).

fof(f100,plain,(
    ! [X2,X1] : k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) = k2_xboole_0(k4_enumset1(sK0,sK0,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)) ),
    inference(superposition,[],[f90,f87])).

fof(f87,plain,(
    ! [X1] : k4_enumset1(sK0,sK0,X1,X1,X1,X1) = k4_enumset1(sK0,sK1,sK1,sK1,sK1,X1) ),
    inference(superposition,[],[f83,f55])).

fof(f90,plain,(
    ! [X2,X1] : k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) = k2_xboole_0(k4_enumset1(sK0,sK1,sK1,sK1,sK1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2)) ),
    inference(superposition,[],[f61,f83])).

fof(f74,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 21:24:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (28976)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (28968)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (28965)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (28984)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.26/0.52  % (28977)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.26/0.52  % (28961)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.26/0.52  % (28969)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.26/0.52  % (28977)Refutation not found, incomplete strategy% (28977)------------------------------
% 1.26/0.52  % (28977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (28962)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (28977)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (28977)Memory used [KB]: 10618
% 1.26/0.53  % (28977)Time elapsed: 0.113 s
% 1.26/0.53  % (28977)------------------------------
% 1.26/0.53  % (28977)------------------------------
% 1.26/0.53  % (28981)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.26/0.53  % (28963)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.53  % (28966)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.53  % (28964)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.53  % (28983)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.43/0.54  % (28979)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.54  % (28978)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.43/0.54  % (28989)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.54  % (28979)Refutation not found, incomplete strategy% (28979)------------------------------
% 1.43/0.54  % (28979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (28979)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (28979)Memory used [KB]: 1663
% 1.43/0.54  % (28979)Time elapsed: 0.126 s
% 1.43/0.54  % (28979)------------------------------
% 1.43/0.54  % (28979)------------------------------
% 1.43/0.54  % (28967)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.54  % (28988)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.54  % (28990)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.54  % (28990)Refutation not found, incomplete strategy% (28990)------------------------------
% 1.43/0.54  % (28990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (28990)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (28990)Memory used [KB]: 1663
% 1.43/0.54  % (28990)Time elapsed: 0.001 s
% 1.43/0.54  % (28990)------------------------------
% 1.43/0.54  % (28990)------------------------------
% 1.43/0.54  % (28987)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.54  % (28975)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.54  % (28970)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.55  % (28962)Refutation not found, incomplete strategy% (28962)------------------------------
% 1.43/0.55  % (28962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28962)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28962)Memory used [KB]: 1663
% 1.43/0.55  % (28962)Time elapsed: 0.132 s
% 1.43/0.55  % (28962)------------------------------
% 1.43/0.55  % (28962)------------------------------
% 1.43/0.55  % (28973)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.55  % (28982)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.55  % (28980)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.55  % (28986)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.55  % (28974)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.55  % (28973)Refutation not found, incomplete strategy% (28973)------------------------------
% 1.43/0.55  % (28973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (28973)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (28973)Memory used [KB]: 10618
% 1.43/0.55  % (28973)Time elapsed: 0.140 s
% 1.43/0.55  % (28973)------------------------------
% 1.43/0.55  % (28973)------------------------------
% 1.43/0.55  % (28972)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.55  % (28971)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.56  % (28987)Refutation not found, incomplete strategy% (28987)------------------------------
% 1.43/0.56  % (28987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (28987)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (28987)Memory used [KB]: 6268
% 1.43/0.56  % (28987)Time elapsed: 0.146 s
% 1.43/0.56  % (28987)------------------------------
% 1.43/0.56  % (28987)------------------------------
% 1.43/0.57  % (28988)Refutation found. Thanks to Tanya!
% 1.43/0.57  % SZS status Theorem for theBenchmark
% 1.43/0.57  % (28985)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.58  % SZS output start Proof for theBenchmark
% 1.43/0.58  fof(f174,plain,(
% 1.43/0.58    $false),
% 1.43/0.58    inference(subsumption_resolution,[],[f171,f25])).
% 1.43/0.58  fof(f25,plain,(
% 1.43/0.58    sK0 != sK1),
% 1.43/0.58    inference(cnf_transformation,[],[f22])).
% 1.43/0.58  fof(f22,plain,(
% 1.43/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.43/0.58    inference(ennf_transformation,[],[f21])).
% 1.43/0.58  fof(f21,negated_conjecture,(
% 1.43/0.58    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.43/0.58    inference(negated_conjecture,[],[f20])).
% 1.43/0.58  fof(f20,conjecture,(
% 1.43/0.58    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.43/0.58  fof(f171,plain,(
% 1.43/0.58    sK0 = sK1),
% 1.43/0.58    inference(resolution,[],[f133,f70])).
% 1.43/0.58  fof(f70,plain,(
% 1.43/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k4_enumset1(X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.43/0.58    inference(equality_resolution,[],[f59])).
% 1.43/0.58  fof(f59,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1) )),
% 1.43/0.58    inference(definition_unfolding,[],[f28,f53])).
% 1.43/0.58  fof(f53,plain,(
% 1.43/0.58    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.43/0.58    inference(definition_unfolding,[],[f31,f52])).
% 1.43/0.58  fof(f52,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.43/0.58    inference(definition_unfolding,[],[f43,f51])).
% 1.43/0.58  fof(f51,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.43/0.58    inference(definition_unfolding,[],[f45,f48])).
% 1.43/0.58  fof(f48,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.43/0.58    inference(definition_unfolding,[],[f44,f47])).
% 1.43/0.58  fof(f47,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f17])).
% 1.43/0.58  fof(f17,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.43/0.58  fof(f44,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f16])).
% 1.43/0.58  fof(f16,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.43/0.58  fof(f45,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f15])).
% 1.43/0.58  fof(f15,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.58  fof(f43,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f14])).
% 1.43/0.58  fof(f14,axiom,(
% 1.43/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.58  fof(f31,plain,(
% 1.43/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f13])).
% 1.43/0.58  fof(f13,axiom,(
% 1.43/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.43/0.58  fof(f28,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f9,axiom,(
% 1.43/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.43/0.58  fof(f133,plain,(
% 1.43/0.58    r2_hidden(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.43/0.58    inference(superposition,[],[f74,f113])).
% 1.43/0.58  fof(f113,plain,(
% 1.43/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.43/0.58    inference(superposition,[],[f105,f86])).
% 1.43/0.58  fof(f86,plain,(
% 1.43/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k4_enumset1(sK0,sK1,sK1,sK1,sK1,sK1)),
% 1.43/0.58    inference(superposition,[],[f83,f56])).
% 1.43/0.58  fof(f56,plain,(
% 1.43/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.43/0.58    inference(definition_unfolding,[],[f24,f53,f53,f53])).
% 1.43/0.58  fof(f24,plain,(
% 1.43/0.58    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.43/0.58    inference(cnf_transformation,[],[f22])).
% 1.43/0.58  fof(f83,plain,(
% 1.43/0.58    ( ! [X0] : (k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(X0,X0,X0,X0,X0,X0)) = k4_enumset1(sK0,sK1,sK1,sK1,sK1,X0)) )),
% 1.43/0.58    inference(forward_demodulation,[],[f82,f55])).
% 1.43/0.58  fof(f55,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f46,f50])).
% 1.43/0.58  fof(f50,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X4,X5,X6))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f33,f49])).
% 1.43/0.58  fof(f49,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f32,f48,f48])).
% 1.43/0.58  fof(f32,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f10])).
% 1.43/0.58  fof(f10,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 1.43/0.58  fof(f33,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f19])).
% 1.43/0.58  fof(f19,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.43/0.58  fof(f46,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f18])).
% 1.43/0.58  fof(f18,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.43/0.58  fof(f82,plain,(
% 1.43/0.58    ( ! [X0] : (k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,X0)) = k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 1.43/0.58    inference(superposition,[],[f61,f56])).
% 1.43/0.58  fof(f61,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)),k4_enumset1(X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f34,f54,f47,f48])).
% 1.43/0.58  fof(f54,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)),k4_enumset1(X8,X8,X8,X8,X8,X8))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f26,f49,f53])).
% 1.43/0.58  fof(f26,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f12])).
% 1.43/0.58  fof(f12,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
% 1.43/0.58  fof(f34,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f11])).
% 1.43/0.58  fof(f11,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 1.43/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 1.43/0.58  fof(f105,plain,(
% 1.43/0.58    ( ! [X0] : (k4_enumset1(sK0,sK1,sK1,sK1,sK1,X0) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0)) )),
% 1.43/0.58    inference(backward_demodulation,[],[f83,f104])).
% 1.43/0.58  fof(f104,plain,(
% 1.43/0.58    ( ! [X2,X1] : (k4_enumset1(sK0,X1,X1,X1,X1,X2) = k2_xboole_0(k4_enumset1(sK0,sK0,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))) )),
% 1.43/0.58    inference(forward_demodulation,[],[f100,f55])).
% 1.43/0.58  fof(f100,plain,(
% 1.43/0.58    ( ! [X2,X1] : (k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) = k2_xboole_0(k4_enumset1(sK0,sK0,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))) )),
% 1.43/0.58    inference(superposition,[],[f90,f87])).
% 1.43/0.58  fof(f87,plain,(
% 1.43/0.58    ( ! [X1] : (k4_enumset1(sK0,sK0,X1,X1,X1,X1) = k4_enumset1(sK0,sK1,sK1,sK1,sK1,X1)) )),
% 1.43/0.58    inference(superposition,[],[f83,f55])).
% 1.43/0.58  fof(f90,plain,(
% 1.43/0.58    ( ! [X2,X1] : (k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) = k2_xboole_0(k4_enumset1(sK0,sK1,sK1,sK1,sK1,X1),k4_enumset1(X2,X2,X2,X2,X2,X2))) )),
% 1.43/0.58    inference(superposition,[],[f61,f83])).
% 1.43/0.59  fof(f74,plain,(
% 1.43/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X1,X4))) )),
% 1.43/0.59    inference(equality_resolution,[],[f73])).
% 1.43/0.59  fof(f73,plain,(
% 1.43/0.59    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k4_enumset1(X0,X0,X0,X0,X1,X4) != X3) )),
% 1.43/0.59    inference(equality_resolution,[],[f62])).
% 1.43/0.59  fof(f62,plain,(
% 1.43/0.59    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 1.43/0.59    inference(definition_unfolding,[],[f42,f51])).
% 1.43/0.59  fof(f42,plain,(
% 1.43/0.59    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.43/0.59    inference(cnf_transformation,[],[f23])).
% 1.43/0.59  fof(f23,plain,(
% 1.43/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.43/0.59    inference(ennf_transformation,[],[f8])).
% 1.43/0.59  fof(f8,axiom,(
% 1.43/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.43/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.43/0.59  % SZS output end Proof for theBenchmark
% 1.43/0.59  % (28988)------------------------------
% 1.43/0.59  % (28988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.59  % (28988)Termination reason: Refutation
% 1.43/0.59  
% 1.43/0.59  % (28988)Memory used [KB]: 6396
% 1.43/0.59  % (28988)Time elapsed: 0.165 s
% 1.43/0.59  % (28988)------------------------------
% 1.43/0.59  % (28988)------------------------------
% 1.43/0.59  % (28960)Success in time 0.231 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:35:39 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 418 expanded)
%              Number of leaves         :   13 ( 134 expanded)
%              Depth                    :   29
%              Number of atoms          :  108 ( 495 expanded)
%              Number of equality atoms :   67 ( 357 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1124,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1123,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f1123,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f1122])).

fof(f1122,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f27,f933])).

fof(f933,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(backward_demodulation,[],[f390,f925])).

fof(f925,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f883,f759])).

fof(f759,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f750,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f750,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f61,f749])).

fof(f749,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(subsumption_resolution,[],[f740,f367])).

fof(f367,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f361,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f361,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f265,f71])).

fof(f71,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f265,plain,(
    ! [X6,X5] : r1_tarski(k1_xboole_0,k5_xboole_0(X6,k3_xboole_0(k1_xboole_0,X5))) ),
    inference(superposition,[],[f215,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f215,plain,(
    ! [X6,X7] : r1_tarski(k1_xboole_0,k5_xboole_0(X7,k4_xboole_0(k1_xboole_0,X6))) ),
    inference(superposition,[],[f187,f37])).

fof(f187,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[],[f102,f33])).

fof(f102,plain,(
    ! [X12,X13] : r1_tarski(k1_xboole_0,k5_xboole_0(X12,k5_xboole_0(X13,k1_xboole_0))) ),
    inference(superposition,[],[f66,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f62,f33])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f30,f61])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f740,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_xboole_0,X0) = X0
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f668,f51])).

fof(f51,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f38,f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f668,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
    inference(forward_demodulation,[],[f667,f28])).

fof(f667,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f666,f37])).

fof(f666,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f663,f33])).

fof(f663,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f368,f662])).

fof(f662,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f661,f28])).

fof(f661,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f645,f367])).

fof(f645,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f115,f51])).

fof(f115,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f63])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f28])).

fof(f368,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f65,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f35,f28])).

fof(f883,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f482,f876])).

fof(f876,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f875,f662])).

fof(f875,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f860,f367])).

fof(f860,plain,(
    ! [X1] :
      ( k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f761,f152])).

fof(f152,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k3_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(backward_demodulation,[],[f70,f151])).

fof(f151,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f138,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f70,f63])).

fof(f70,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f37,f38])).

fof(f761,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f750,f37])).

fof(f482,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f481,f65])).

fof(f481,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f455,f32])).

fof(f455,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(superposition,[],[f92,f151])).

fof(f92,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X10),X11)) = k5_xboole_0(k4_xboole_0(X9,X10),X11) ),
    inference(superposition,[],[f43,f37])).

fof(f390,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(forward_demodulation,[],[f389,f35])).

fof(f389,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X1,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(forward_demodulation,[],[f373,f33])).

fof(f373,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f65,f51])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (5655)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (5668)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (5647)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (5665)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (5647)Refutation not found, incomplete strategy% (5647)------------------------------
% 0.21/0.53  % (5647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5647)Memory used [KB]: 1663
% 0.21/0.53  % (5647)Time elapsed: 0.107 s
% 0.21/0.53  % (5647)------------------------------
% 0.21/0.53  % (5647)------------------------------
% 0.21/0.53  % (5652)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (5654)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (5646)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (5657)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (5656)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (5657)Refutation not found, incomplete strategy% (5657)------------------------------
% 0.21/0.54  % (5657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5657)Memory used [KB]: 6140
% 0.21/0.54  % (5657)Time elapsed: 0.125 s
% 0.21/0.54  % (5657)------------------------------
% 0.21/0.54  % (5657)------------------------------
% 0.21/0.54  % (5660)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (5656)Refutation not found, incomplete strategy% (5656)------------------------------
% 0.21/0.54  % (5656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5656)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5656)Memory used [KB]: 10618
% 0.21/0.54  % (5656)Time elapsed: 0.117 s
% 0.21/0.54  % (5656)------------------------------
% 0.21/0.54  % (5656)------------------------------
% 0.21/0.54  % (5650)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (5662)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (5663)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (5669)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (5653)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (5648)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (5649)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (5664)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (5670)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (5664)Refutation not found, incomplete strategy% (5664)------------------------------
% 0.21/0.55  % (5664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5664)Memory used [KB]: 1663
% 0.21/0.55  % (5664)Time elapsed: 0.134 s
% 0.21/0.55  % (5664)------------------------------
% 0.21/0.55  % (5664)------------------------------
% 0.21/0.55  % (5674)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (5651)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (5671)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (5660)Refutation not found, incomplete strategy% (5660)------------------------------
% 0.21/0.55  % (5660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5674)Refutation not found, incomplete strategy% (5674)------------------------------
% 0.21/0.55  % (5674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5674)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5674)Memory used [KB]: 10618
% 0.21/0.55  % (5674)Time elapsed: 0.105 s
% 0.21/0.55  % (5674)------------------------------
% 0.21/0.55  % (5674)------------------------------
% 0.21/0.56  % (5661)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (5666)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (5667)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (5675)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (5659)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (5660)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5660)Memory used [KB]: 1663
% 0.21/0.56  % (5660)Time elapsed: 0.115 s
% 0.21/0.56  % (5660)------------------------------
% 0.21/0.56  % (5660)------------------------------
% 0.21/0.56  % (5675)Refutation not found, incomplete strategy% (5675)------------------------------
% 0.21/0.56  % (5675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5675)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5675)Memory used [KB]: 1663
% 0.21/0.56  % (5675)Time elapsed: 0.147 s
% 0.21/0.56  % (5675)------------------------------
% 0.21/0.56  % (5675)------------------------------
% 0.21/0.56  % (5673)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (5663)Refutation not found, incomplete strategy% (5663)------------------------------
% 0.21/0.56  % (5663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5663)Memory used [KB]: 1663
% 0.21/0.56  % (5663)Time elapsed: 0.136 s
% 0.21/0.56  % (5663)------------------------------
% 0.21/0.56  % (5663)------------------------------
% 0.21/0.56  % (5673)Refutation not found, incomplete strategy% (5673)------------------------------
% 0.21/0.56  % (5673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5658)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % (5662)Refutation not found, incomplete strategy% (5662)------------------------------
% 0.21/0.57  % (5662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5670)Refutation not found, incomplete strategy% (5670)------------------------------
% 0.21/0.57  % (5670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  % (5670)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  
% 0.21/0.57  % (5670)Memory used [KB]: 10618
% 0.21/0.57  % (5662)Memory used [KB]: 10618
% 0.21/0.57  % (5662)Time elapsed: 0.146 s
% 0.21/0.57  % (5670)Time elapsed: 0.145 s
% 0.21/0.57  % (5662)------------------------------
% 0.21/0.57  % (5662)------------------------------
% 0.21/0.57  % (5670)------------------------------
% 0.21/0.57  % (5670)------------------------------
% 0.21/0.57  % (5658)Refutation not found, incomplete strategy% (5658)------------------------------
% 0.21/0.57  % (5658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5658)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5658)Memory used [KB]: 10618
% 0.21/0.57  % (5658)Time elapsed: 0.156 s
% 0.21/0.57  % (5658)------------------------------
% 0.21/0.57  % (5658)------------------------------
% 0.21/0.57  % (5673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5673)Memory used [KB]: 6140
% 0.21/0.57  % (5673)Time elapsed: 0.143 s
% 0.21/0.57  % (5673)------------------------------
% 0.21/0.57  % (5673)------------------------------
% 1.67/0.58  % (5671)Refutation not found, incomplete strategy% (5671)------------------------------
% 1.67/0.58  % (5671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (5671)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (5671)Memory used [KB]: 6140
% 1.67/0.58  % (5671)Time elapsed: 0.151 s
% 1.67/0.58  % (5671)------------------------------
% 1.67/0.58  % (5671)------------------------------
% 1.67/0.58  % (5672)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.67/0.58  % (5672)Refutation not found, incomplete strategy% (5672)------------------------------
% 1.67/0.58  % (5672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (5672)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.60  
% 1.67/0.60  % (5672)Memory used [KB]: 6140
% 1.67/0.60  % (5672)Time elapsed: 0.166 s
% 1.67/0.60  % (5672)------------------------------
% 1.67/0.60  % (5672)------------------------------
% 1.85/0.61  % (5655)Refutation found. Thanks to Tanya!
% 1.85/0.61  % SZS status Theorem for theBenchmark
% 1.85/0.62  % SZS output start Proof for theBenchmark
% 1.85/0.62  fof(f1124,plain,(
% 1.85/0.62    $false),
% 1.85/0.62    inference(subsumption_resolution,[],[f1123,f31])).
% 1.85/0.62  fof(f31,plain,(
% 1.85/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.85/0.62    inference(cnf_transformation,[],[f18])).
% 1.85/0.62  fof(f18,axiom,(
% 1.85/0.62    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.85/0.62  fof(f1123,plain,(
% 1.85/0.62    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.85/0.62    inference(trivial_inequality_removal,[],[f1122])).
% 1.85/0.62  fof(f1122,plain,(
% 1.85/0.62    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.85/0.62    inference(superposition,[],[f27,f933])).
% 1.85/0.62  fof(f933,plain,(
% 1.85/0.62    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X0 | ~r1_tarski(X1,X0)) )),
% 1.85/0.62    inference(backward_demodulation,[],[f390,f925])).
% 1.85/0.62  fof(f925,plain,(
% 1.85/0.62    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.85/0.62    inference(forward_demodulation,[],[f883,f759])).
% 1.85/0.62  fof(f759,plain,(
% 1.85/0.62    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.85/0.62    inference(superposition,[],[f750,f33])).
% 1.85/0.62  fof(f33,plain,(
% 1.85/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f2])).
% 1.85/0.62  fof(f2,axiom,(
% 1.85/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.85/0.62  fof(f750,plain,(
% 1.85/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.85/0.62    inference(backward_demodulation,[],[f61,f749])).
% 1.85/0.62  fof(f749,plain,(
% 1.85/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.85/0.62    inference(subsumption_resolution,[],[f740,f367])).
% 1.85/0.62  fof(f367,plain,(
% 1.85/0.62    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.85/0.62    inference(forward_demodulation,[],[f361,f28])).
% 1.85/0.62  fof(f28,plain,(
% 1.85/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.85/0.62    inference(cnf_transformation,[],[f6])).
% 1.85/0.62  fof(f6,axiom,(
% 1.85/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.85/0.62  fof(f361,plain,(
% 1.85/0.62    ( ! [X1] : (r1_tarski(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.85/0.62    inference(superposition,[],[f265,f71])).
% 1.85/0.62  fof(f71,plain,(
% 1.85/0.62    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X5,X4))) )),
% 1.85/0.62    inference(superposition,[],[f37,f32])).
% 1.85/0.62  fof(f32,plain,(
% 1.85/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f1])).
% 1.85/0.62  fof(f1,axiom,(
% 1.85/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.85/0.62  fof(f37,plain,(
% 1.85/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.85/0.62    inference(cnf_transformation,[],[f4])).
% 1.85/0.63  fof(f4,axiom,(
% 1.85/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.85/0.63  fof(f265,plain,(
% 1.85/0.63    ( ! [X6,X5] : (r1_tarski(k1_xboole_0,k5_xboole_0(X6,k3_xboole_0(k1_xboole_0,X5)))) )),
% 1.85/0.63    inference(superposition,[],[f215,f36])).
% 1.85/0.63  fof(f36,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f7])).
% 1.85/0.63  fof(f7,axiom,(
% 1.85/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.85/0.63  fof(f215,plain,(
% 1.85/0.63    ( ! [X6,X7] : (r1_tarski(k1_xboole_0,k5_xboole_0(X7,k4_xboole_0(k1_xboole_0,X6)))) )),
% 1.85/0.63    inference(superposition,[],[f187,f37])).
% 1.85/0.63  fof(f187,plain,(
% 1.85/0.63    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X1)))) )),
% 1.85/0.63    inference(superposition,[],[f102,f33])).
% 1.85/0.63  fof(f102,plain,(
% 1.85/0.63    ( ! [X12,X13] : (r1_tarski(k1_xboole_0,k5_xboole_0(X12,k5_xboole_0(X13,k1_xboole_0)))) )),
% 1.85/0.63    inference(superposition,[],[f66,f43])).
% 1.85/0.63  fof(f43,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f9])).
% 1.85/0.63  fof(f9,axiom,(
% 1.85/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.85/0.63  fof(f66,plain,(
% 1.85/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 1.85/0.63    inference(superposition,[],[f62,f33])).
% 1.85/0.63  fof(f62,plain,(
% 1.85/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.85/0.63    inference(superposition,[],[f30,f61])).
% 1.85/0.63  fof(f30,plain,(
% 1.85/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f8])).
% 1.85/0.63  fof(f8,axiom,(
% 1.85/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.85/0.63  fof(f740,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0 | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.85/0.63    inference(superposition,[],[f668,f51])).
% 1.85/0.63  fof(f51,plain,(
% 1.85/0.63    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.85/0.63    inference(superposition,[],[f38,f32])).
% 1.85/0.63  fof(f38,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f22])).
% 1.85/0.63  fof(f22,plain,(
% 1.85/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.85/0.63    inference(ennf_transformation,[],[f5])).
% 1.85/0.63  fof(f5,axiom,(
% 1.85/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.85/0.63  fof(f668,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0) )),
% 1.85/0.63    inference(forward_demodulation,[],[f667,f28])).
% 1.85/0.63  fof(f667,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) )),
% 1.85/0.63    inference(forward_demodulation,[],[f666,f37])).
% 1.85/0.63  fof(f666,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 1.85/0.63    inference(forward_demodulation,[],[f663,f33])).
% 1.85/0.63  fof(f663,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) )),
% 1.85/0.63    inference(backward_demodulation,[],[f368,f662])).
% 1.85/0.63  fof(f662,plain,(
% 1.85/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.85/0.63    inference(forward_demodulation,[],[f661,f28])).
% 1.85/0.63  fof(f661,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 1.85/0.63    inference(subsumption_resolution,[],[f645,f367])).
% 1.85/0.63  fof(f645,plain,(
% 1.85/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.85/0.63    inference(superposition,[],[f115,f51])).
% 1.85/0.63  fof(f115,plain,(
% 1.85/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 1.85/0.63    inference(superposition,[],[f36,f63])).
% 1.85/0.63  fof(f63,plain,(
% 1.85/0.63    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.85/0.63    inference(superposition,[],[f36,f28])).
% 1.85/0.63  fof(f368,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X0))) )),
% 1.85/0.63    inference(superposition,[],[f65,f63])).
% 1.85/0.63  fof(f65,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.85/0.63    inference(superposition,[],[f35,f36])).
% 1.85/0.63  fof(f35,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f10])).
% 1.85/0.63  fof(f10,axiom,(
% 1.85/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.85/0.63  fof(f61,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.85/0.63    inference(superposition,[],[f35,f28])).
% 1.85/0.63  fof(f883,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.85/0.63    inference(backward_demodulation,[],[f482,f876])).
% 1.85/0.63  fof(f876,plain,(
% 1.85/0.63    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.85/0.63    inference(forward_demodulation,[],[f875,f662])).
% 1.85/0.63  fof(f875,plain,(
% 1.85/0.63    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.85/0.63    inference(subsumption_resolution,[],[f860,f367])).
% 1.85/0.63  fof(f860,plain,(
% 1.85/0.63    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X1)) )),
% 1.85/0.63    inference(superposition,[],[f761,f152])).
% 1.85/0.63  fof(f152,plain,(
% 1.85/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X2,X3)) )),
% 1.85/0.63    inference(backward_demodulation,[],[f70,f151])).
% 1.85/0.63  fof(f151,plain,(
% 1.85/0.63    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) )),
% 1.85/0.63    inference(subsumption_resolution,[],[f138,f48])).
% 1.85/0.63  fof(f48,plain,(
% 1.85/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.85/0.63    inference(equality_resolution,[],[f40])).
% 1.85/0.63  fof(f40,plain,(
% 1.85/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.85/0.63    inference(cnf_transformation,[],[f26])).
% 1.85/0.63  fof(f26,plain,(
% 1.85/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/0.63    inference(flattening,[],[f25])).
% 1.85/0.63  fof(f25,plain,(
% 1.85/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/0.63    inference(nnf_transformation,[],[f3])).
% 1.85/0.63  fof(f3,axiom,(
% 1.85/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.85/0.63  fof(f138,plain,(
% 1.85/0.63    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.85/0.63    inference(superposition,[],[f70,f63])).
% 1.85/0.63  fof(f70,plain,(
% 1.85/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 1.85/0.63    inference(superposition,[],[f37,f38])).
% 1.85/0.63  fof(f761,plain,(
% 1.85/0.63    ( ! [X3] : (k3_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.85/0.63    inference(superposition,[],[f750,f37])).
% 1.85/0.63  fof(f482,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)))) )),
% 1.85/0.63    inference(forward_demodulation,[],[f481,f65])).
% 1.85/0.63  fof(f481,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)))) )),
% 1.85/0.63    inference(forward_demodulation,[],[f455,f32])).
% 1.85/0.63  fof(f455,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0))) )),
% 1.85/0.63    inference(superposition,[],[f92,f151])).
% 1.85/0.63  fof(f92,plain,(
% 1.85/0.63    ( ! [X10,X11,X9] : (k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X10),X11)) = k5_xboole_0(k4_xboole_0(X9,X10),X11)) )),
% 1.85/0.63    inference(superposition,[],[f43,f37])).
% 1.85/0.63  fof(f390,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) )),
% 1.85/0.63    inference(forward_demodulation,[],[f389,f35])).
% 1.85/0.63  fof(f389,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) | ~r1_tarski(X1,X0)) )),
% 1.85/0.63    inference(forward_demodulation,[],[f373,f33])).
% 1.85/0.63  fof(f373,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),X1) | ~r1_tarski(X1,X0)) )),
% 1.85/0.63    inference(superposition,[],[f65,f51])).
% 1.85/0.63  fof(f27,plain,(
% 1.85/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.85/0.63    inference(cnf_transformation,[],[f24])).
% 1.85/0.63  fof(f24,plain,(
% 1.85/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.85/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 1.85/0.63  fof(f23,plain,(
% 1.85/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.85/0.63    introduced(choice_axiom,[])).
% 1.85/0.63  fof(f21,plain,(
% 1.85/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.85/0.63    inference(ennf_transformation,[],[f20])).
% 1.85/0.63  fof(f20,negated_conjecture,(
% 1.85/0.63    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.85/0.63    inference(negated_conjecture,[],[f19])).
% 1.85/0.63  fof(f19,conjecture,(
% 1.85/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.85/0.63  % SZS output end Proof for theBenchmark
% 1.85/0.63  % (5655)------------------------------
% 1.85/0.63  % (5655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.63  % (5655)Termination reason: Refutation
% 1.85/0.63  
% 1.85/0.63  % (5655)Memory used [KB]: 2942
% 1.85/0.63  % (5655)Time elapsed: 0.185 s
% 1.85/0.63  % (5655)------------------------------
% 1.85/0.63  % (5655)------------------------------
% 1.85/0.63  % (5645)Success in time 0.263 s
%------------------------------------------------------------------------------

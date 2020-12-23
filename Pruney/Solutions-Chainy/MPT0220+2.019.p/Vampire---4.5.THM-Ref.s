%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:39 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 392 expanded)
%              Number of leaves         :   12 ( 126 expanded)
%              Depth                    :   27
%              Number of atoms          :   83 ( 463 expanded)
%              Number of equality atoms :   63 ( 365 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25866)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f784,plain,(
    $false ),
    inference(subsumption_resolution,[],[f783,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f783,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f782])).

fof(f782,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f27,f575])).

fof(f575,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(backward_demodulation,[],[f444,f568])).

fof(f568,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f64,f567])).

fof(f567,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f535,f202])).

fof(f202,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f200,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f200,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f61,f199])).

fof(f199,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(subsumption_resolution,[],[f193,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f193,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_xboole_0,X0) = X0
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f128,f51])).

fof(f51,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

fof(f128,plain,(
    ! [X1] : k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) = X1 ),
    inference(forward_demodulation,[],[f127,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f127,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f126,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f126,plain,(
    ! [X1] : k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f125,f33])).

fof(f125,plain,(
    ! [X1] : k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) = k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f115,f117])).

fof(f117,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f116,f29])).

fof(f116,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f109,f28])).

fof(f109,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f66,f51])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f29])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f115,plain,(
    ! [X1] : k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) = k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f35,f66])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f35,f29])).

fof(f535,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f85,f347])).

fof(f347,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f131,f342])).

fof(f342,plain,(
    ! [X5] : k1_xboole_0 = k3_xboole_0(X5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f206,f338])).

fof(f338,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f205,f337])).

fof(f337,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f336,f117])).

fof(f336,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f322,f28])).

fof(f322,plain,(
    ! [X1] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X1)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f205,f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k3_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(backward_demodulation,[],[f72,f131])).

fof(f72,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f37,f38])).

fof(f205,plain,(
    ! [X4] : k3_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f200,f37])).

fof(f206,plain,(
    ! [X5] : k3_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f200,f73])).

fof(f73,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f37,f32])).

fof(f131,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f129,f62])).

fof(f129,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f73,f117])).

fof(f85,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X10),X11)) = k5_xboole_0(k4_xboole_0(X9,X10),X11) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f36])).

fof(f444,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(forward_demodulation,[],[f443,f35])).

fof(f443,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X1,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(forward_demodulation,[],[f419,f33])).

fof(f419,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f64,f51])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:31:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (25851)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (25856)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (25852)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (25864)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (25872)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (25872)Refutation not found, incomplete strategy% (25872)------------------------------
% 0.22/0.52  % (25872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25864)Refutation not found, incomplete strategy% (25864)------------------------------
% 0.22/0.52  % (25864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25872)Memory used [KB]: 6140
% 0.22/0.52  % (25872)Time elapsed: 0.107 s
% 0.22/0.52  % (25872)------------------------------
% 0.22/0.52  % (25872)------------------------------
% 0.22/0.52  % (25864)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25864)Memory used [KB]: 1663
% 0.22/0.52  % (25864)Time elapsed: 0.106 s
% 0.22/0.52  % (25864)------------------------------
% 0.22/0.52  % (25864)------------------------------
% 0.22/0.52  % (25848)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (25848)Refutation not found, incomplete strategy% (25848)------------------------------
% 0.22/0.52  % (25848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25848)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25848)Memory used [KB]: 1663
% 0.22/0.52  % (25848)Time elapsed: 0.076 s
% 0.22/0.52  % (25848)------------------------------
% 0.22/0.52  % (25848)------------------------------
% 0.22/0.53  % (25849)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (25853)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (25862)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.54  % (25868)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.54  % (25855)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.54  % (25861)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.54  % (25861)Refutation not found, incomplete strategy% (25861)------------------------------
% 1.39/0.54  % (25861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (25861)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (25861)Memory used [KB]: 1663
% 1.39/0.54  % (25861)Time elapsed: 0.128 s
% 1.39/0.54  % (25861)------------------------------
% 1.39/0.54  % (25861)------------------------------
% 1.39/0.54  % (25870)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.54  % (25854)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.54  % (25869)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.39/0.54  % (25875)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.55  % (25875)Refutation not found, incomplete strategy% (25875)------------------------------
% 1.39/0.55  % (25875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25875)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25875)Memory used [KB]: 10618
% 1.39/0.55  % (25875)Time elapsed: 0.131 s
% 1.39/0.55  % (25875)------------------------------
% 1.39/0.55  % (25875)------------------------------
% 1.39/0.55  % (25874)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.55  % (25874)Refutation not found, incomplete strategy% (25874)------------------------------
% 1.39/0.55  % (25874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25874)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25874)Memory used [KB]: 6140
% 1.39/0.55  % (25874)Time elapsed: 0.129 s
% 1.39/0.55  % (25874)------------------------------
% 1.39/0.55  % (25874)------------------------------
% 1.39/0.55  % (25847)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.55  % (25876)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (25867)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (25865)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.55  % (25876)Refutation not found, incomplete strategy% (25876)------------------------------
% 1.39/0.55  % (25876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25876)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25876)Memory used [KB]: 1663
% 1.39/0.55  % (25876)Time elapsed: 0.140 s
% 1.39/0.55  % (25876)------------------------------
% 1.39/0.55  % (25876)------------------------------
% 1.39/0.55  % (25865)Refutation not found, incomplete strategy% (25865)------------------------------
% 1.39/0.55  % (25865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25865)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25865)Memory used [KB]: 1663
% 1.39/0.55  % (25865)Time elapsed: 0.140 s
% 1.39/0.55  % (25865)------------------------------
% 1.39/0.55  % (25865)------------------------------
% 1.39/0.55  % (25871)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.55  % (25860)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.55  % (25857)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.55  % (25871)Refutation not found, incomplete strategy% (25871)------------------------------
% 1.39/0.55  % (25871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25871)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25871)Memory used [KB]: 10618
% 1.39/0.55  % (25871)Time elapsed: 0.140 s
% 1.39/0.55  % (25871)------------------------------
% 1.39/0.55  % (25871)------------------------------
% 1.39/0.55  % (25857)Refutation not found, incomplete strategy% (25857)------------------------------
% 1.39/0.55  % (25857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25857)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25857)Memory used [KB]: 10618
% 1.39/0.55  % (25857)Time elapsed: 0.107 s
% 1.39/0.55  % (25857)------------------------------
% 1.39/0.55  % (25857)------------------------------
% 1.39/0.55  % (25859)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.54/0.55  % (25859)Refutation not found, incomplete strategy% (25859)------------------------------
% 1.54/0.55  % (25859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  % (25859)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.55  
% 1.54/0.55  % (25859)Memory used [KB]: 10618
% 1.54/0.55  % (25859)Time elapsed: 0.142 s
% 1.54/0.55  % (25859)------------------------------
% 1.54/0.55  % (25859)------------------------------
% 1.54/0.56  % (25873)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.54/0.56  % (25873)Refutation not found, incomplete strategy% (25873)------------------------------
% 1.54/0.56  % (25873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (25873)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (25873)Memory used [KB]: 6140
% 1.54/0.56  % (25873)Time elapsed: 0.147 s
% 1.54/0.56  % (25873)------------------------------
% 1.54/0.56  % (25873)------------------------------
% 1.54/0.56  % (25863)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.54/0.56  % (25863)Refutation not found, incomplete strategy% (25863)------------------------------
% 1.54/0.56  % (25863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (25863)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (25863)Memory used [KB]: 10618
% 1.54/0.56  % (25863)Time elapsed: 0.148 s
% 1.54/0.56  % (25863)------------------------------
% 1.54/0.56  % (25863)------------------------------
% 1.54/0.57  % (25850)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.54/0.57  % (25856)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  % (25866)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.57  fof(f784,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(subsumption_resolution,[],[f783,f31])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f18])).
% 1.54/0.57  fof(f18,axiom,(
% 1.54/0.57    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.54/0.57  fof(f783,plain,(
% 1.54/0.57    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f782])).
% 1.54/0.57  fof(f782,plain,(
% 1.54/0.57    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.54/0.57    inference(superposition,[],[f27,f575])).
% 1.54/0.57  fof(f575,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X0 | ~r1_tarski(X1,X0)) )),
% 1.54/0.57    inference(backward_demodulation,[],[f444,f568])).
% 1.54/0.57  fof(f568,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.54/0.57    inference(backward_demodulation,[],[f64,f567])).
% 1.54/0.57  fof(f567,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 1.54/0.57    inference(forward_demodulation,[],[f535,f202])).
% 1.54/0.57  fof(f202,plain,(
% 1.54/0.57    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.54/0.57    inference(superposition,[],[f200,f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.54/0.57  fof(f200,plain,(
% 1.54/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.57    inference(backward_demodulation,[],[f61,f199])).
% 1.54/0.57  fof(f199,plain,(
% 1.54/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f193,f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.54/0.57  fof(f193,plain,(
% 1.54/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0 | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.57    inference(superposition,[],[f128,f51])).
% 1.54/0.57  fof(f51,plain,(
% 1.54/0.57    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.54/0.57    inference(superposition,[],[f38,f32])).
% 1.54/0.57  fof(f32,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f22,plain,(
% 1.54/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f5])).
% 1.54/0.58  fof(f5,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.58  fof(f128,plain,(
% 1.54/0.58    ( ! [X1] : (k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) = X1) )),
% 1.54/0.58    inference(forward_demodulation,[],[f127,f29])).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.54/0.58  fof(f127,plain,(
% 1.54/0.58    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f126,f37])).
% 1.54/0.58  fof(f37,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.58  fof(f126,plain,(
% 1.54/0.58    ( ! [X1] : (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f125,f33])).
% 1.54/0.58  fof(f125,plain,(
% 1.54/0.58    ( ! [X1] : (k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) = k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f115,f117])).
% 1.54/0.58  fof(f117,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.58    inference(forward_demodulation,[],[f116,f29])).
% 1.54/0.58  fof(f116,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f109,f28])).
% 1.54/0.58  fof(f109,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.58    inference(superposition,[],[f66,f51])).
% 1.54/0.58  fof(f66,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 1.54/0.58    inference(superposition,[],[f36,f62])).
% 1.54/0.58  fof(f62,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(superposition,[],[f36,f29])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.58  fof(f115,plain,(
% 1.54/0.58    ( ! [X1] : (k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) = k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X1,X1))) )),
% 1.54/0.58    inference(superposition,[],[f35,f66])).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.54/0.58  fof(f61,plain,(
% 1.54/0.58    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.58    inference(superposition,[],[f35,f29])).
% 1.54/0.58  fof(f535,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(superposition,[],[f85,f347])).
% 1.54/0.58  fof(f347,plain,(
% 1.54/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(backward_demodulation,[],[f131,f342])).
% 1.54/0.58  fof(f342,plain,(
% 1.54/0.58    ( ! [X5] : (k1_xboole_0 = k3_xboole_0(X5,k1_xboole_0)) )),
% 1.54/0.58    inference(backward_demodulation,[],[f206,f338])).
% 1.54/0.58  fof(f338,plain,(
% 1.54/0.58    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.54/0.58    inference(backward_demodulation,[],[f205,f337])).
% 1.54/0.58  fof(f337,plain,(
% 1.54/0.58    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f336,f117])).
% 1.54/0.58  fof(f336,plain,(
% 1.54/0.58    ( ! [X1] : (k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f322,f28])).
% 1.54/0.58  fof(f322,plain,(
% 1.54/0.58    ( ! [X1] : (k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X1) | ~r1_tarski(k1_xboole_0,X1)) )),
% 1.54/0.58    inference(superposition,[],[f205,f132])).
% 1.54/0.58  fof(f132,plain,(
% 1.54/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X2,X3)) )),
% 1.54/0.58    inference(backward_demodulation,[],[f72,f131])).
% 1.54/0.58  fof(f72,plain,(
% 1.54/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 1.54/0.58    inference(superposition,[],[f37,f38])).
% 1.54/0.58  fof(f205,plain,(
% 1.54/0.58    ( ! [X4] : (k3_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.54/0.58    inference(superposition,[],[f200,f37])).
% 1.54/0.58  fof(f206,plain,(
% 1.54/0.58    ( ! [X5] : (k3_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X5)) )),
% 1.54/0.58    inference(superposition,[],[f200,f73])).
% 1.54/0.58  fof(f73,plain,(
% 1.54/0.58    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X5,X4))) )),
% 1.54/0.58    inference(superposition,[],[f37,f32])).
% 1.54/0.58  fof(f131,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f129,f62])).
% 1.54/0.58  fof(f129,plain,(
% 1.54/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(superposition,[],[f73,f117])).
% 1.54/0.58  fof(f85,plain,(
% 1.54/0.58    ( ! [X10,X11,X9] : (k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X10),X11)) = k5_xboole_0(k4_xboole_0(X9,X10),X11)) )),
% 1.54/0.58    inference(superposition,[],[f43,f37])).
% 1.54/0.58  fof(f43,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f9])).
% 1.54/0.58  fof(f9,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.58  fof(f64,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(superposition,[],[f35,f36])).
% 1.54/0.58  fof(f444,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f443,f35])).
% 1.54/0.58  fof(f443,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) | ~r1_tarski(X1,X0)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f419,f33])).
% 1.54/0.58  fof(f419,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),X1) | ~r1_tarski(X1,X0)) )),
% 1.54/0.58    inference(superposition,[],[f64,f51])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.54/0.58    inference(cnf_transformation,[],[f24])).
% 1.54/0.58  fof(f24,plain,(
% 1.54/0.58    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 1.54/0.58  fof(f23,plain,(
% 1.54/0.58    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f21,plain,(
% 1.54/0.58    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f20])).
% 1.54/0.58  fof(f20,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.54/0.58    inference(negated_conjecture,[],[f19])).
% 1.54/0.58  fof(f19,conjecture,(
% 1.54/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (25856)------------------------------
% 1.54/0.58  % (25856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (25856)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (25856)Memory used [KB]: 2558
% 1.54/0.58  % (25856)Time elapsed: 0.146 s
% 1.54/0.58  % (25856)------------------------------
% 1.54/0.58  % (25856)------------------------------
% 1.54/0.58  % (25846)Success in time 0.208 s
%------------------------------------------------------------------------------

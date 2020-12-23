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
% DateTime   : Thu Dec  3 12:38:47 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 132 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 187 expanded)
%              Number of equality atoms :   60 ( 126 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f51])).

fof(f51,plain,(
    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f27,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f358,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f353,f49])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f30,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f353,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f136,f165])).

fof(f165,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f163,f156])).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f83,f154])).

fof(f154,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f73,f153])).

fof(f153,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f140,f152])).

fof(f152,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4 ),
    inference(forward_demodulation,[],[f147,f49])).

fof(f147,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f36,f78])).

fof(f78,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f71,f49])).

fof(f71,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f49,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f140,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f34,f72])).

fof(f72,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f49,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f35,f49])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f83,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f34,f56])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f38,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f163,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f34,f93])).

fof(f93,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f82,f38])).

fof(f82,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f81,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f81,plain,(
    r1_tarski(k2_tarski(sK0,sK0),sK1) ),
    inference(resolution,[],[f80,f26])).

fof(f26,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k2_tarski(X0,sK0),sK1) ) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f136,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f135,f116])).

fof(f116,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f115,f37])).

fof(f115,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f107,f30])).

fof(f107,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,X6),X6) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f64,f37])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f63,f36])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f36,f35])).

fof(f135,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f127,f37])).

fof(f127,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f37,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f35,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (15239)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (15243)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (15255)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (15259)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.24/0.53  % (15261)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.24/0.53  % (15251)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.24/0.53  % (15261)Refutation not found, incomplete strategy% (15261)------------------------------
% 1.24/0.53  % (15261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (15261)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (15261)Memory used [KB]: 1663
% 1.24/0.53  % (15261)Time elapsed: 0.115 s
% 1.24/0.53  % (15261)------------------------------
% 1.24/0.53  % (15261)------------------------------
% 1.24/0.53  % (15253)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.24/0.54  % (15259)Refutation not found, incomplete strategy% (15259)------------------------------
% 1.24/0.54  % (15259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (15259)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (15259)Memory used [KB]: 6140
% 1.24/0.54  % (15259)Time elapsed: 0.118 s
% 1.24/0.54  % (15259)------------------------------
% 1.24/0.54  % (15259)------------------------------
% 1.24/0.54  % (15239)Refutation found. Thanks to Tanya!
% 1.24/0.54  % SZS status Theorem for theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f359,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(subsumption_resolution,[],[f358,f51])).
% 1.24/0.54  fof(f51,plain,(
% 1.24/0.54    sK1 != k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.24/0.54    inference(superposition,[],[f27,f30])).
% 1.24/0.54  fof(f30,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.24/0.54  fof(f27,plain,(
% 1.24/0.54    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.24/0.54    inference(cnf_transformation,[],[f21])).
% 1.24/0.54  fof(f21,plain,(
% 1.24/0.54    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.24/0.54    inference(ennf_transformation,[],[f17])).
% 1.24/0.54  fof(f17,negated_conjecture,(
% 1.24/0.54    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.24/0.54    inference(negated_conjecture,[],[f16])).
% 1.24/0.54  fof(f16,conjecture,(
% 1.24/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.24/0.54  fof(f358,plain,(
% 1.24/0.54    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.24/0.54    inference(forward_demodulation,[],[f353,f49])).
% 1.24/0.54  fof(f49,plain,(
% 1.24/0.54    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.24/0.54    inference(superposition,[],[f30,f28])).
% 1.24/0.54  fof(f28,plain,(
% 1.24/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f4])).
% 1.24/0.54  fof(f4,axiom,(
% 1.24/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.24/0.54  fof(f353,plain,(
% 1.24/0.54    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(k1_xboole_0,sK1)),
% 1.24/0.54    inference(superposition,[],[f136,f165])).
% 1.24/0.54  fof(f165,plain,(
% 1.24/0.54    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.24/0.54    inference(forward_demodulation,[],[f163,f156])).
% 1.24/0.54  fof(f156,plain,(
% 1.24/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.24/0.54    inference(backward_demodulation,[],[f83,f154])).
% 1.24/0.54  fof(f154,plain,(
% 1.24/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.24/0.54    inference(backward_demodulation,[],[f73,f153])).
% 1.24/0.54  fof(f153,plain,(
% 1.24/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.24/0.54    inference(backward_demodulation,[],[f140,f152])).
% 1.24/0.54  fof(f152,plain,(
% 1.24/0.54    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = X4) )),
% 1.24/0.54    inference(forward_demodulation,[],[f147,f49])).
% 1.24/0.54  fof(f147,plain,(
% 1.24/0.54    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,X4)) )),
% 1.24/0.54    inference(superposition,[],[f36,f78])).
% 1.24/0.54  fof(f78,plain,(
% 1.24/0.54    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.24/0.54    inference(forward_demodulation,[],[f71,f49])).
% 1.24/0.54  fof(f71,plain,(
% 1.24/0.54    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X3)) )),
% 1.24/0.54    inference(superposition,[],[f49,f37])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f7])).
% 1.24/0.54  fof(f7,axiom,(
% 1.24/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.24/0.54  fof(f36,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,axiom,(
% 1.24/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.24/0.54  fof(f140,plain,(
% 1.24/0.54    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.24/0.54    inference(superposition,[],[f34,f72])).
% 1.24/0.54  fof(f72,plain,(
% 1.24/0.54    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 1.24/0.54    inference(superposition,[],[f49,f31])).
% 1.24/0.54  fof(f31,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f5])).
% 1.24/0.54  fof(f5,axiom,(
% 1.24/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.24/0.54  fof(f34,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.54  fof(f73,plain,(
% 1.24/0.54    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 1.24/0.54    inference(superposition,[],[f35,f49])).
% 1.24/0.54  fof(f35,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f8])).
% 1.24/0.54  fof(f8,axiom,(
% 1.24/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.24/0.54  fof(f83,plain,(
% 1.24/0.54    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.24/0.54    inference(superposition,[],[f34,f56])).
% 1.24/0.54  fof(f56,plain,(
% 1.24/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.24/0.54    inference(resolution,[],[f38,f47])).
% 1.24/0.54  fof(f47,plain,(
% 1.24/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.54    inference(equality_resolution,[],[f40])).
% 1.24/0.54  fof(f40,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.24/0.54    inference(cnf_transformation,[],[f23])).
% 1.24/0.54  fof(f23,plain,(
% 1.24/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.54    inference(flattening,[],[f22])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.54    inference(nnf_transformation,[],[f2])).
% 1.24/0.54  fof(f2,axiom,(
% 1.24/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.54  fof(f38,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.24/0.54    inference(cnf_transformation,[],[f19])).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.24/0.54    inference(ennf_transformation,[],[f6])).
% 1.24/0.54  fof(f6,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.24/0.54  fof(f163,plain,(
% 1.24/0.54    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.24/0.54    inference(superposition,[],[f34,f93])).
% 1.24/0.54  fof(f93,plain,(
% 1.24/0.54    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.24/0.54    inference(resolution,[],[f82,f38])).
% 1.24/0.54  fof(f82,plain,(
% 1.24/0.54    r1_tarski(k1_tarski(sK0),sK1)),
% 1.24/0.54    inference(forward_demodulation,[],[f81,f29])).
% 1.24/0.54  fof(f29,plain,(
% 1.24/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f10])).
% 1.24/0.54  fof(f10,axiom,(
% 1.24/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.54  fof(f81,plain,(
% 1.24/0.54    r1_tarski(k2_tarski(sK0,sK0),sK1)),
% 1.24/0.54    inference(resolution,[],[f80,f26])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    r2_hidden(sK0,sK1)),
% 1.24/0.54    inference(cnf_transformation,[],[f21])).
% 1.24/0.54  fof(f80,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_tarski(X0,sK0),sK1)) )),
% 1.24/0.54    inference(resolution,[],[f45,f26])).
% 1.24/0.54  fof(f45,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f25])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.24/0.54    inference(flattening,[],[f24])).
% 1.24/0.54  fof(f24,plain,(
% 1.24/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.24/0.54    inference(nnf_transformation,[],[f15])).
% 1.24/0.54  fof(f15,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.24/0.54  fof(f136,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 1.24/0.54    inference(forward_demodulation,[],[f135,f116])).
% 1.24/0.54  fof(f116,plain,(
% 1.24/0.54    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 1.24/0.54    inference(forward_demodulation,[],[f115,f37])).
% 1.24/0.54  fof(f115,plain,(
% 1.24/0.54    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 1.24/0.54    inference(forward_demodulation,[],[f107,f30])).
% 1.24/0.54  fof(f107,plain,(
% 1.24/0.54    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,X6),X6) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 1.24/0.54    inference(superposition,[],[f64,f37])).
% 1.24/0.54  fof(f64,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 1.24/0.54    inference(forward_demodulation,[],[f63,f36])).
% 1.24/0.54  fof(f63,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.24/0.54    inference(superposition,[],[f36,f35])).
% 1.24/0.54  fof(f135,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 1.24/0.54    inference(forward_demodulation,[],[f127,f37])).
% 1.24/0.54  fof(f127,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.24/0.54    inference(superposition,[],[f37,f66])).
% 1.24/0.54  fof(f66,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.24/0.54    inference(superposition,[],[f35,f37])).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (15239)------------------------------
% 1.24/0.54  % (15239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (15239)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (15239)Memory used [KB]: 1918
% 1.24/0.54  % (15239)Time elapsed: 0.112 s
% 1.24/0.54  % (15239)------------------------------
% 1.24/0.54  % (15239)------------------------------
% 1.24/0.54  % (15231)Success in time 0.173 s
%------------------------------------------------------------------------------

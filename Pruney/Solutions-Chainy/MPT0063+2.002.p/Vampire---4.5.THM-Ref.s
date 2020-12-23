%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 119 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :   95 ( 294 expanded)
%              Number of equality atoms :   35 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(subsumption_resolution,[],[f140,f84])).

fof(f84,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f68,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f68,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f35,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f19,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f61,plain,
    ( r2_xboole_0(sK1,sK0)
    | k1_xboole_0 != k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f20,f47])).

fof(f47,plain,
    ( sK0 = sK2
    | k1_xboole_0 != k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f21,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f140,plain,(
    r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f23,f123])).

fof(f123,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f122,f56])).

fof(f56,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f54,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f54,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f25,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f37,f31])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f122,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f114,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f114,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f78,f52])).

fof(f52,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f50,f22])).

fof(f50,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f25,f41])).

fof(f41,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f34,f31])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f19,f27])).

fof(f78,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,X0) ),
    inference(superposition,[],[f32,f56])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (9508)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.42  % (9508)Refutation not found, incomplete strategy% (9508)------------------------------
% 0.21/0.42  % (9508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (9508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (9508)Memory used [KB]: 1535
% 0.21/0.42  % (9508)Time elapsed: 0.003 s
% 0.21/0.42  % (9508)------------------------------
% 0.21/0.42  % (9508)------------------------------
% 0.22/0.46  % (9502)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (9495)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (9509)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (9501)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (9515)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (9515)Refutation not found, incomplete strategy% (9515)------------------------------
% 0.22/0.53  % (9515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9515)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9515)Memory used [KB]: 10490
% 0.22/0.53  % (9515)Time elapsed: 0.090 s
% 0.22/0.53  % (9515)------------------------------
% 0.22/0.53  % (9515)------------------------------
% 0.22/0.53  % (9499)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (9498)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (9499)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ~r1_tarski(sK0,sK2)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,sK2)),
% 0.22/0.53    inference(superposition,[],[f68,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    k1_xboole_0 != k4_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f61,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~r2_xboole_0(sK1,sK0)),
% 0.22/0.53    inference(resolution,[],[f19,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    r2_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    r2_xboole_0(sK1,sK0) | k1_xboole_0 != k4_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(superposition,[],[f20,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    sK0 = sK2 | k1_xboole_0 != k4_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(resolution,[],[f40,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ~r1_tarski(sK0,sK2) | sK0 = sK2),
% 0.22/0.53    inference(resolution,[],[f21,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    r2_xboole_0(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    r1_tarski(sK0,sK2)),
% 0.22/0.53    inference(superposition,[],[f23,f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    sK2 = k2_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f122,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    sK2 = k2_xboole_0(sK2,sK1)),
% 0.22/0.53    inference(forward_demodulation,[],[f54,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f25,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.22/0.53    inference(resolution,[],[f37,f31])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2)),
% 0.22/0.53    inference(resolution,[],[f20,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f114,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,sK0)),
% 0.22/0.53    inference(superposition,[],[f78,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(sK1,sK0)),
% 0.22/0.53    inference(forward_demodulation,[],[f50,f22])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f25,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f34,f31])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    r1_tarski(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f19,f27])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,X0)) )),
% 0.22/0.53    inference(superposition,[],[f32,f56])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (9499)------------------------------
% 0.22/0.53  % (9499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9499)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (9499)Memory used [KB]: 1663
% 0.22/0.53  % (9499)Time elapsed: 0.089 s
% 0.22/0.53  % (9499)------------------------------
% 0.22/0.53  % (9499)------------------------------
% 0.22/0.53  % (9507)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (9494)Success in time 0.174 s
%------------------------------------------------------------------------------

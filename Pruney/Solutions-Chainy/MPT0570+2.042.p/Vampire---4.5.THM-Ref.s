%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  95 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 239 expanded)
%              Number of equality atoms :   50 ( 121 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(subsumption_resolution,[],[f174,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f174,plain,(
    k1_xboole_0 = sK0 ),
    inference(superposition,[],[f173,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f54,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f173,plain,(
    ! [X0] : k4_xboole_0(X0,sK0) = X0 ),
    inference(backward_demodulation,[],[f170,f172])).

fof(f172,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f171,f33])).

fof(f171,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f169,f33])).

fof(f169,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,k4_xboole_0(X5,k1_xboole_0))) ),
    inference(resolution,[],[f43,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f48,f63])).

fof(f63,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f61,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f47,f29])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f38,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f170,plain,(
    ! [X0] : k4_xboole_0(X0,sK0) = k2_xboole_0(k4_xboole_0(X0,k2_relat_1(sK1)),k3_xboole_0(X0,k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f167,f69])).

fof(f69,plain,(
    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(resolution,[],[f68,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f68,plain,(
    r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f67,f25])).

fof(f67,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f167,plain,(
    ! [X0] : k4_xboole_0(X0,sK0) = k2_xboole_0(k4_xboole_0(X0,k2_relat_1(sK1)),k3_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),sK0))) ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17461)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (17478)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (17470)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (17462)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (17478)Refutation not found, incomplete strategy% (17478)------------------------------
% 0.22/0.51  % (17478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17458)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (17459)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (17463)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (17478)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17478)Memory used [KB]: 10618
% 0.22/0.52  % (17478)Time elapsed: 0.051 s
% 0.22/0.52  % (17478)------------------------------
% 0.22/0.52  % (17478)------------------------------
% 0.22/0.52  % (17463)Refutation not found, incomplete strategy% (17463)------------------------------
% 0.22/0.52  % (17463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17463)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17463)Memory used [KB]: 10746
% 0.22/0.52  % (17463)Time elapsed: 0.109 s
% 0.22/0.52  % (17463)------------------------------
% 0.22/0.52  % (17463)------------------------------
% 0.22/0.52  % (17455)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (17456)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (17480)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (17462)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f174,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    k1_xboole_0 = sK0),
% 0.22/0.52    inference(superposition,[],[f173,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f54,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f36,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,sK0) = X0) )),
% 0.22/0.52    inference(backward_demodulation,[],[f170,f172])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4) )),
% 0.22/0.52    inference(forward_demodulation,[],[f171,f33])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f169,f33])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,k4_xboole_0(X5,k1_xboole_0)))) )),
% 0.22/0.52    inference(resolution,[],[f43,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f48,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    v1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f61,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X2] : (~v1_relat_1(X2) | v1_relat_1(k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f37,f58])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f47,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f38,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) | ~r1_tarski(X2,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,sK0) = k2_xboole_0(k4_xboole_0(X0,k2_relat_1(sK1)),k3_xboole_0(X0,k2_relat_1(sK1)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f167,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.53    inference(resolution,[],[f68,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f67,f25])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.53    inference(superposition,[],[f39,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,sK0) = k2_xboole_0(k4_xboole_0(X0,k2_relat_1(sK1)),k3_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),sK0)))) )),
% 0.22/0.53    inference(resolution,[],[f43,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (17462)------------------------------
% 0.22/0.53  % (17462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17462)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (17462)Memory used [KB]: 6268
% 0.22/0.53  % (17462)Time elapsed: 0.063 s
% 0.22/0.53  % (17462)------------------------------
% 0.22/0.53  % (17462)------------------------------
% 0.22/0.53  % (17460)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (17453)Success in time 0.165 s
%------------------------------------------------------------------------------

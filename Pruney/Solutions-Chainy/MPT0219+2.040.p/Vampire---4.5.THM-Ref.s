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
% DateTime   : Thu Dec  3 12:35:25 EST 2020

% Result     : Theorem 3.28s
% Output     : Refutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 152 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 178 expanded)
%              Number of equality atoms :   59 ( 166 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f852,plain,(
    $false ),
    inference(subsumption_resolution,[],[f849,f26])).

fof(f26,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f849,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f845,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f845,plain,(
    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f89,f495])).

fof(f495,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f67,f68])).

fof(f68,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f25,f65,f59,f65,f65])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f57,f59,f56,f65])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f89,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (27232)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (27225)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (27248)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (27229)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (27230)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (27233)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (27249)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (27228)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (27227)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (27249)Refutation not found, incomplete strategy% (27249)------------------------------
% 0.21/0.52  % (27249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27226)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (27249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27249)Memory used [KB]: 10746
% 0.21/0.52  % (27249)Time elapsed: 0.107 s
% 0.21/0.52  % (27249)------------------------------
% 0.21/0.52  % (27249)------------------------------
% 0.21/0.52  % (27226)Refutation not found, incomplete strategy% (27226)------------------------------
% 0.21/0.52  % (27226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27226)Memory used [KB]: 1663
% 0.21/0.52  % (27226)Time elapsed: 0.105 s
% 0.21/0.52  % (27226)------------------------------
% 0.21/0.52  % (27226)------------------------------
% 0.21/0.52  % (27253)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (27247)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (27239)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (27240)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (27231)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (27237)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (27245)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (27241)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (27241)Refutation not found, incomplete strategy% (27241)------------------------------
% 0.21/0.53  % (27241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27241)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27241)Memory used [KB]: 10618
% 0.21/0.53  % (27241)Time elapsed: 0.095 s
% 0.21/0.53  % (27241)------------------------------
% 0.21/0.53  % (27241)------------------------------
% 0.21/0.53  % (27252)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (27252)Refutation not found, incomplete strategy% (27252)------------------------------
% 0.21/0.53  % (27252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27252)Memory used [KB]: 6140
% 0.21/0.53  % (27252)Time elapsed: 0.128 s
% 0.21/0.53  % (27252)------------------------------
% 0.21/0.53  % (27252)------------------------------
% 0.21/0.53  % (27251)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (27251)Refutation not found, incomplete strategy% (27251)------------------------------
% 0.21/0.54  % (27251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27251)Memory used [KB]: 6140
% 0.21/0.54  % (27251)Time elapsed: 0.128 s
% 0.21/0.54  % (27251)------------------------------
% 0.21/0.54  % (27251)------------------------------
% 0.21/0.54  % (27242)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (27250)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.54  % (27234)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.54  % (27254)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.46/0.54  % (27239)Refutation not found, incomplete strategy% (27239)------------------------------
% 1.46/0.54  % (27239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (27239)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (27239)Memory used [KB]: 1663
% 1.46/0.54  % (27239)Time elapsed: 0.092 s
% 1.46/0.54  % (27239)------------------------------
% 1.46/0.54  % (27239)------------------------------
% 1.46/0.54  % (27246)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.54  % (27250)Refutation not found, incomplete strategy% (27250)------------------------------
% 1.46/0.54  % (27250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (27250)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (27250)Memory used [KB]: 6140
% 1.46/0.54  % (27250)Time elapsed: 0.126 s
% 1.46/0.54  % (27250)------------------------------
% 1.46/0.54  % (27250)------------------------------
% 1.46/0.54  % (27244)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.54  % (27243)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.55  % (27243)Refutation not found, incomplete strategy% (27243)------------------------------
% 1.46/0.55  % (27243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (27243)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (27243)Memory used [KB]: 1663
% 1.46/0.55  % (27243)Time elapsed: 0.139 s
% 1.46/0.55  % (27243)------------------------------
% 1.46/0.55  % (27243)------------------------------
% 1.46/0.55  % (27237)Refutation not found, incomplete strategy% (27237)------------------------------
% 1.46/0.55  % (27237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (27237)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (27237)Memory used [KB]: 10618
% 1.46/0.55  % (27237)Time elapsed: 0.144 s
% 1.46/0.55  % (27237)------------------------------
% 1.46/0.55  % (27237)------------------------------
% 1.46/0.55  % (27235)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.46/0.55  % (27254)Refutation not found, incomplete strategy% (27254)------------------------------
% 1.46/0.55  % (27254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (27254)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (27254)Memory used [KB]: 1663
% 1.46/0.55  % (27254)Time elapsed: 0.003 s
% 1.46/0.55  % (27254)------------------------------
% 1.46/0.55  % (27254)------------------------------
% 1.46/0.55  % (27238)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.55  % (27242)Refutation not found, incomplete strategy% (27242)------------------------------
% 1.46/0.55  % (27242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (27242)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (27242)Memory used [KB]: 1791
% 1.46/0.55  % (27242)Time elapsed: 0.128 s
% 1.46/0.55  % (27242)------------------------------
% 1.46/0.55  % (27242)------------------------------
% 1.46/0.55  % (27236)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.55  % (27236)Refutation not found, incomplete strategy% (27236)------------------------------
% 1.46/0.55  % (27236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (27236)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (27236)Memory used [KB]: 6268
% 1.46/0.55  % (27236)Time elapsed: 0.139 s
% 1.46/0.55  % (27236)------------------------------
% 1.46/0.55  % (27236)------------------------------
% 1.63/0.62  % (27225)Refutation not found, incomplete strategy% (27225)------------------------------
% 1.63/0.62  % (27225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.62  % (27225)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.62  
% 1.63/0.62  % (27225)Memory used [KB]: 1663
% 1.63/0.62  % (27225)Time elapsed: 0.186 s
% 1.63/0.62  % (27225)------------------------------
% 1.63/0.62  % (27225)------------------------------
% 2.01/0.63  % (27255)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.01/0.65  % (27228)Refutation not found, incomplete strategy% (27228)------------------------------
% 2.01/0.65  % (27228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.65  % (27228)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.65  
% 2.01/0.65  % (27228)Memory used [KB]: 6140
% 2.01/0.65  % (27228)Time elapsed: 0.237 s
% 2.01/0.65  % (27228)------------------------------
% 2.01/0.65  % (27228)------------------------------
% 2.01/0.66  % (27256)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.01/0.66  % (27257)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.21/0.67  % (27258)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.21/0.67  % (27259)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.21/0.67  % (27227)Refutation not found, incomplete strategy% (27227)------------------------------
% 2.21/0.67  % (27227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.67  % (27257)Refutation not found, incomplete strategy% (27257)------------------------------
% 2.21/0.67  % (27257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.67  % (27257)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.67  
% 2.21/0.67  % (27257)Memory used [KB]: 6140
% 2.21/0.67  % (27257)Time elapsed: 0.082 s
% 2.21/0.67  % (27257)------------------------------
% 2.21/0.67  % (27257)------------------------------
% 2.21/0.67  % (27262)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.21/0.68  % (27261)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.21/0.68  % (27240)Refutation not found, incomplete strategy% (27240)------------------------------
% 2.21/0.68  % (27240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (27259)Refutation not found, incomplete strategy% (27259)------------------------------
% 2.21/0.68  % (27259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (27259)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.68  
% 2.21/0.68  % (27259)Memory used [KB]: 10746
% 2.21/0.68  % (27259)Time elapsed: 0.110 s
% 2.21/0.68  % (27259)------------------------------
% 2.21/0.68  % (27259)------------------------------
% 2.21/0.68  % (27265)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.21/0.68  % (27258)Refutation not found, incomplete strategy% (27258)------------------------------
% 2.21/0.68  % (27258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (27258)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.68  
% 2.21/0.68  % (27258)Memory used [KB]: 10746
% 2.21/0.68  % (27258)Time elapsed: 0.110 s
% 2.21/0.68  % (27258)------------------------------
% 2.21/0.68  % (27258)------------------------------
% 2.21/0.68  % (27263)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.21/0.68  % (27264)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.21/0.68  % (27260)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.21/0.68  % (27227)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.68  
% 2.21/0.68  % (27227)Memory used [KB]: 6396
% 2.21/0.68  % (27227)Time elapsed: 0.241 s
% 2.21/0.68  % (27227)------------------------------
% 2.21/0.68  % (27227)------------------------------
% 2.21/0.68  % (27264)Refutation not found, incomplete strategy% (27264)------------------------------
% 2.21/0.68  % (27264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (27264)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.68  
% 2.21/0.68  % (27264)Memory used [KB]: 10746
% 2.21/0.68  % (27264)Time elapsed: 0.112 s
% 2.21/0.68  % (27264)------------------------------
% 2.21/0.68  % (27264)------------------------------
% 2.21/0.69  % (27266)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.21/0.69  % (27261)Refutation not found, incomplete strategy% (27261)------------------------------
% 2.21/0.69  % (27261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.69  % (27261)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.69  
% 2.21/0.69  % (27261)Memory used [KB]: 10746
% 2.21/0.69  % (27261)Time elapsed: 0.115 s
% 2.21/0.69  % (27261)------------------------------
% 2.21/0.69  % (27261)------------------------------
% 2.21/0.70  % (27240)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.70  
% 2.21/0.70  % (27240)Memory used [KB]: 6140
% 2.21/0.70  % (27240)Time elapsed: 0.265 s
% 2.21/0.70  % (27240)------------------------------
% 2.21/0.70  % (27240)------------------------------
% 2.21/0.73  % (27267)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.85/0.78  % (27268)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.85/0.78  % (27268)Refutation not found, incomplete strategy% (27268)------------------------------
% 2.85/0.78  % (27268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.78  % (27268)Termination reason: Refutation not found, incomplete strategy
% 2.85/0.78  
% 2.85/0.78  % (27268)Memory used [KB]: 10746
% 2.85/0.78  % (27268)Time elapsed: 0.100 s
% 2.85/0.78  % (27268)------------------------------
% 2.85/0.78  % (27268)------------------------------
% 2.85/0.81  % (27269)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.85/0.81  % (27272)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.85/0.81  % (27271)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.85/0.81  % (27270)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.85/0.82  % (27273)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.16/0.83  % (27274)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.16/0.84  % (27275)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.28/0.86  % (27272)Refutation found. Thanks to Tanya!
% 3.28/0.86  % SZS status Theorem for theBenchmark
% 3.28/0.86  % SZS output start Proof for theBenchmark
% 3.28/0.86  fof(f852,plain,(
% 3.28/0.86    $false),
% 3.28/0.86    inference(subsumption_resolution,[],[f849,f26])).
% 3.28/0.86  fof(f26,plain,(
% 3.28/0.86    sK0 != sK1),
% 3.28/0.86    inference(cnf_transformation,[],[f23])).
% 3.28/0.86  fof(f23,plain,(
% 3.28/0.86    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.28/0.86    inference(ennf_transformation,[],[f21])).
% 3.28/0.86  fof(f21,negated_conjecture,(
% 3.28/0.86    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.28/0.86    inference(negated_conjecture,[],[f20])).
% 3.28/0.86  fof(f20,conjecture,(
% 3.28/0.86    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 3.28/0.86  fof(f849,plain,(
% 3.28/0.86    sK0 = sK1),
% 3.28/0.86    inference(resolution,[],[f845,f85])).
% 3.28/0.86  fof(f85,plain,(
% 3.28/0.86    ( ! [X2,X0] : (~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 3.28/0.86    inference(equality_resolution,[],[f71])).
% 3.28/0.86  fof(f71,plain,(
% 3.28/0.86    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.28/0.86    inference(definition_unfolding,[],[f38,f65])).
% 3.28/0.86  fof(f65,plain,(
% 3.28/0.86    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.28/0.86    inference(definition_unfolding,[],[f28,f64])).
% 3.28/0.86  fof(f64,plain,(
% 3.28/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.28/0.86    inference(definition_unfolding,[],[f31,f63])).
% 3.28/0.86  fof(f63,plain,(
% 3.28/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.28/0.86    inference(definition_unfolding,[],[f43,f62])).
% 3.28/0.86  fof(f62,plain,(
% 3.28/0.86    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.28/0.86    inference(definition_unfolding,[],[f45,f61])).
% 3.28/0.86  fof(f61,plain,(
% 3.28/0.86    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.28/0.86    inference(definition_unfolding,[],[f54,f60])).
% 3.28/0.86  fof(f60,plain,(
% 3.28/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.28/0.86    inference(definition_unfolding,[],[f55,f56])).
% 3.28/0.86  fof(f56,plain,(
% 3.28/0.86    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.28/0.86    inference(cnf_transformation,[],[f19])).
% 3.28/0.86  fof(f19,axiom,(
% 3.28/0.86    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.28/0.86  fof(f55,plain,(
% 3.28/0.86    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.28/0.86    inference(cnf_transformation,[],[f18])).
% 3.28/0.86  fof(f18,axiom,(
% 3.28/0.86    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.28/0.86  fof(f54,plain,(
% 3.28/0.86    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.28/0.86    inference(cnf_transformation,[],[f17])).
% 3.28/0.86  fof(f17,axiom,(
% 3.28/0.86    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.28/0.86  fof(f45,plain,(
% 3.28/0.86    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.28/0.86    inference(cnf_transformation,[],[f16])).
% 3.28/0.86  fof(f16,axiom,(
% 3.28/0.86    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.28/0.86  fof(f43,plain,(
% 3.28/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.28/0.86    inference(cnf_transformation,[],[f15])).
% 3.28/0.86  fof(f15,axiom,(
% 3.28/0.86    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.28/0.86  fof(f31,plain,(
% 3.28/0.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.28/0.86    inference(cnf_transformation,[],[f14])).
% 3.28/0.86  fof(f14,axiom,(
% 3.28/0.86    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.28/0.86  fof(f28,plain,(
% 3.28/0.86    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.28/0.86    inference(cnf_transformation,[],[f13])).
% 3.28/0.86  fof(f13,axiom,(
% 3.28/0.86    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.28/0.86  fof(f38,plain,(
% 3.28/0.86    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 3.28/0.86    inference(cnf_transformation,[],[f10])).
% 3.28/0.86  fof(f10,axiom,(
% 3.28/0.86    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 3.28/0.86  fof(f845,plain,(
% 3.28/0.86    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 3.28/0.86    inference(superposition,[],[f89,f495])).
% 3.28/0.86  fof(f495,plain,(
% 3.28/0.86    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 3.28/0.86    inference(superposition,[],[f67,f68])).
% 3.28/0.86  fof(f68,plain,(
% 3.28/0.86    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 3.28/0.86    inference(definition_unfolding,[],[f25,f65,f59,f65,f65])).
% 3.28/0.86  fof(f59,plain,(
% 3.28/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.28/0.86    inference(definition_unfolding,[],[f33,f32])).
% 3.28/0.86  fof(f32,plain,(
% 3.28/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.28/0.86    inference(cnf_transformation,[],[f5])).
% 3.28/0.86  fof(f5,axiom,(
% 3.28/0.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.28/0.86  fof(f33,plain,(
% 3.28/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.28/0.86    inference(cnf_transformation,[],[f8])).
% 3.28/0.86  fof(f8,axiom,(
% 3.28/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.28/0.86  fof(f25,plain,(
% 3.28/0.86    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 3.28/0.86    inference(cnf_transformation,[],[f23])).
% 3.28/0.86  fof(f67,plain,(
% 3.28/0.86    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 3.28/0.86    inference(definition_unfolding,[],[f57,f59,f56,f65])).
% 3.28/0.86  fof(f57,plain,(
% 3.28/0.86    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 3.28/0.86    inference(cnf_transformation,[],[f12])).
% 3.28/0.86  fof(f12,axiom,(
% 3.28/0.86    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 3.28/0.86  fof(f89,plain,(
% 3.28/0.86    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4))) )),
% 3.28/0.86    inference(equality_resolution,[],[f88])).
% 3.28/0.86  fof(f88,plain,(
% 3.28/0.86    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3) )),
% 3.28/0.86    inference(equality_resolution,[],[f75])).
% 3.28/0.86  fof(f75,plain,(
% 3.28/0.86    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.28/0.86    inference(definition_unfolding,[],[f53,f63])).
% 3.28/0.86  fof(f53,plain,(
% 3.28/0.86    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.28/0.86    inference(cnf_transformation,[],[f24])).
% 3.28/0.86  fof(f24,plain,(
% 3.28/0.86    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.28/0.86    inference(ennf_transformation,[],[f9])).
% 3.28/0.86  fof(f9,axiom,(
% 3.28/0.86    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.28/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 3.28/0.86  % SZS output end Proof for theBenchmark
% 3.28/0.86  % (27272)------------------------------
% 3.28/0.86  % (27272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.86  % (27272)Termination reason: Refutation
% 3.28/0.86  
% 3.28/0.86  % (27272)Memory used [KB]: 6908
% 3.28/0.86  % (27272)Time elapsed: 0.137 s
% 3.28/0.86  % (27272)------------------------------
% 3.28/0.86  % (27272)------------------------------
% 3.28/0.87  % (27224)Success in time 0.497 s
%------------------------------------------------------------------------------

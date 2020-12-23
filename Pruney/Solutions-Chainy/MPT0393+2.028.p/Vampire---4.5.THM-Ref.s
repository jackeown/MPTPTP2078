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
% DateTime   : Thu Dec  3 12:45:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 729 expanded)
%              Number of leaves         :   11 ( 229 expanded)
%              Depth                    :   19
%              Number of atoms          :  125 (1091 expanded)
%              Number of equality atoms :   52 ( 654 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f321,plain,(
    $false ),
    inference(resolution,[],[f263,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f263,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f177,f259])).

fof(f259,plain,(
    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f46,f178,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ r2_hidden(X2,X0)
      | X1 = X2 ) ),
    inference(global_subsumption,[],[f59,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | X1 = X2
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(superposition,[],[f43,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f59,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(superposition,[],[f49,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f46,f29])).

fof(f49,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f178,plain,(
    r2_hidden(sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f51,f172,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f172,plain,(
    ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f161,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f161,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f46,f136,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f136,plain,(
    ! [X0] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(backward_demodulation,[],[f77,f135])).

fof(f135,plain,(
    ! [X4] : sK2(k2_enumset1(X4,X4,X4,X4),k1_xboole_0) = X4 ),
    inference(global_subsumption,[],[f51,f133])).

fof(f133,plain,(
    ! [X4] :
      ( sK2(k2_enumset1(X4,X4,X4,X4),k1_xboole_0) = X4
      | k1_xboole_0 = k2_enumset1(X4,X4,X4,X4) ) ),
    inference(resolution,[],[f118,f90])).

fof(f90,plain,(
    ! [X3] :
      ( r2_hidden(sK2(X3,k1_xboole_0),X3)
      | k1_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f89,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f67,f59,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f67,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) ),
    inference(unit_resulting_resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,k1_xboole_0),X3)
      | k4_xboole_0(k1_xboole_0,k2_enumset1(X4,X4,X4,X4)) = X3 ) ),
    inference(forward_demodulation,[],[f81,f78])).

fof(f81,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,k4_xboole_0(k1_xboole_0,k2_enumset1(X4,X4,X4,X4))),X3)
      | k4_xboole_0(k1_xboole_0,k2_enumset1(X4,X4,X4,X4)) = X3 ) ),
    inference(resolution,[],[f24,f67])).

fof(f118,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k2_enumset1(X3,X3,X3,X3))
      | X3 = X4 ) ),
    inference(global_subsumption,[],[f59,f115])).

fof(f115,plain,(
    ! [X4,X3] :
      ( r2_hidden(X4,k1_xboole_0)
      | X3 = X4
      | ~ r2_hidden(X4,k2_enumset1(X3,X3,X3,X3)) ) ),
    inference(superposition,[],[f43,f50])).

fof(f77,plain,(
    ! [X0] : r2_hidden(sK2(k2_enumset1(X0,X0,X0,X0),k1_xboole_0),k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f51,f59,f24])).

fof(f40,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f19,f39])).

fof(f19,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f51,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f48,f50])).

fof(f48,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f32,f39,f39,f39])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f177,plain,(
    ~ r1_tarski(sK0,sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)) ),
    inference(unit_resulting_resolution,[],[f51,f172,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (2491)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.45  % (2491)Refutation not found, incomplete strategy% (2491)------------------------------
% 0.21/0.45  % (2491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (2491)Memory used [KB]: 10618
% 0.21/0.46  % (2491)Time elapsed: 0.066 s
% 0.21/0.46  % (2491)------------------------------
% 0.21/0.46  % (2491)------------------------------
% 0.21/0.47  % (2506)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.47  % (2506)Refutation not found, incomplete strategy% (2506)------------------------------
% 0.21/0.47  % (2506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2506)Memory used [KB]: 10618
% 0.21/0.48  % (2506)Time elapsed: 0.083 s
% 0.21/0.48  % (2506)------------------------------
% 0.21/0.48  % (2506)------------------------------
% 0.21/0.48  % (2499)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (2499)Refutation not found, incomplete strategy% (2499)------------------------------
% 0.21/0.48  % (2499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2499)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2499)Memory used [KB]: 10618
% 0.21/0.48  % (2499)Time elapsed: 0.083 s
% 0.21/0.48  % (2499)------------------------------
% 0.21/0.48  % (2499)------------------------------
% 0.21/0.49  % (2501)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (2490)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (2493)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (2503)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (2510)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (2489)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (2489)Refutation not found, incomplete strategy% (2489)------------------------------
% 0.21/0.51  % (2489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2489)Memory used [KB]: 1663
% 0.21/0.51  % (2489)Time elapsed: 0.098 s
% 0.21/0.51  % (2489)------------------------------
% 0.21/0.51  % (2489)------------------------------
% 0.21/0.51  % (2498)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (2514)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (2495)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (2494)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2497)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (2513)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (2511)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (2505)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (2515)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (2518)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (2497)Refutation not found, incomplete strategy% (2497)------------------------------
% 0.21/0.52  % (2497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2497)Memory used [KB]: 10618
% 0.21/0.52  % (2497)Time elapsed: 0.110 s
% 0.21/0.52  % (2497)------------------------------
% 0.21/0.52  % (2497)------------------------------
% 0.21/0.52  % (2498)Refutation not found, incomplete strategy% (2498)------------------------------
% 0.21/0.52  % (2498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2492)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (2498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2498)Memory used [KB]: 10618
% 0.21/0.52  % (2498)Time elapsed: 0.124 s
% 0.21/0.52  % (2498)------------------------------
% 0.21/0.52  % (2498)------------------------------
% 0.21/0.52  % (2510)Refutation not found, incomplete strategy% (2510)------------------------------
% 0.21/0.52  % (2510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2510)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2510)Memory used [KB]: 1663
% 0.21/0.52  % (2510)Time elapsed: 0.096 s
% 0.21/0.52  % (2510)------------------------------
% 0.21/0.52  % (2510)------------------------------
% 0.21/0.52  % (2502)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (2496)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (2512)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (2513)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f321,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(resolution,[],[f263,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ~r1_tarski(sK0,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f177,f259])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f178,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | ~r2_hidden(X2,X0) | X1 = X2) )),
% 0.21/0.53    inference(global_subsumption,[],[f59,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_xboole_0) | X1 = X2 | ~r2_hidden(X2,X0) | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.53    inference(superposition,[],[f43,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f49,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f29])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f39])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    r2_hidden(sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f51,f172,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f40,f161,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f136,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f77,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ( ! [X4] : (sK2(k2_enumset1(X4,X4,X4,X4),k1_xboole_0) = X4) )),
% 0.21/0.53    inference(global_subsumption,[],[f51,f133])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X4] : (sK2(k2_enumset1(X4,X4,X4,X4),k1_xboole_0) = X4 | k1_xboole_0 = k2_enumset1(X4,X4,X4,X4)) )),
% 0.21/0.53    inference(resolution,[],[f118,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X3] : (r2_hidden(sK2(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) )),
% 0.21/0.53    inference(forward_demodulation,[],[f89,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f67,f59,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f59,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f35,f39])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X4,X3] : (r2_hidden(sK2(X3,k1_xboole_0),X3) | k4_xboole_0(k1_xboole_0,k2_enumset1(X4,X4,X4,X4)) = X3) )),
% 0.21/0.53    inference(forward_demodulation,[],[f81,f78])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X4,X3] : (r2_hidden(sK2(X3,k4_xboole_0(k1_xboole_0,k2_enumset1(X4,X4,X4,X4))),X3) | k4_xboole_0(k1_xboole_0,k2_enumset1(X4,X4,X4,X4)) = X3) )),
% 0.21/0.53    inference(resolution,[],[f24,f67])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k2_enumset1(X3,X3,X3,X3)) | X3 = X4) )),
% 0.21/0.53    inference(global_subsumption,[],[f59,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X4,X3] : (r2_hidden(X4,k1_xboole_0) | X3 = X4 | ~r2_hidden(X4,k2_enumset1(X3,X3,X3,X3))) )),
% 0.21/0.53    inference(superposition,[],[f43,f50])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(k2_enumset1(X0,X0,X0,X0),k1_xboole_0),k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f51,f59,f24])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f39])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f48,f50])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f39,f39,f39])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ~r1_tarski(sK0,sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f51,f172,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2513)------------------------------
% 0.21/0.53  % (2513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2513)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2513)Memory used [KB]: 6524
% 0.21/0.53  % (2513)Time elapsed: 0.121 s
% 0.21/0.53  % (2513)------------------------------
% 0.21/0.53  % (2513)------------------------------
% 0.21/0.53  % (2512)Refutation not found, incomplete strategy% (2512)------------------------------
% 0.21/0.53  % (2512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2511)Refutation not found, incomplete strategy% (2511)------------------------------
% 0.21/0.53  % (2511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2511)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2511)Memory used [KB]: 10618
% 0.21/0.53  % (2511)Time elapsed: 0.104 s
% 0.21/0.53  % (2511)------------------------------
% 0.21/0.53  % (2511)------------------------------
% 0.21/0.53  % (2504)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (2512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2512)Memory used [KB]: 1663
% 0.21/0.53  % (2512)Time elapsed: 0.121 s
% 0.21/0.53  % (2512)------------------------------
% 0.21/0.53  % (2512)------------------------------
% 0.21/0.53  % (2500)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (2508)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (2507)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (2516)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (2509)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (2509)Refutation not found, incomplete strategy% (2509)------------------------------
% 0.21/0.54  % (2509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2488)Success in time 0.186 s
%------------------------------------------------------------------------------

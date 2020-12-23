%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:15 EST 2020

% Result     : Theorem 2.56s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 191 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  156 ( 413 expanded)
%              Number of equality atoms :   56 ( 160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4420,plain,(
    $false ),
    inference(resolution,[],[f4356,f2725])).

fof(f2725,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2718,f78])).

fof(f78,plain,(
    k3_xboole_0(sK1,sK2) != k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f18,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f50,plain,(
    k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f20,f49])).

fof(f20,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f2718,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f219,f2671])).

fof(f2671,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f2640,f86])).

fof(f86,plain,(
    r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f73,f79])).

fof(f79,plain,(
    r2_hidden(sK3,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f66,f51])).

fof(f66,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2640,plain,(
    ! [X65] :
      ( ~ r2_hidden(sK3,X65)
      | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,X65)) ) ),
    inference(resolution,[],[f549,f19])).

fof(f19,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f549,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(sK3,X19)
      | ~ r2_hidden(sK3,X20)
      | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X19,X20)) ) ),
    inference(resolution,[],[f533,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f533,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3,X3)
      | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X3) ) ),
    inference(subsumption_resolution,[],[f530,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f530,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3,X3)
      | r1_tarski(k3_xboole_0(sK1,sK2),X3)
      | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X3) ) ),
    inference(superposition,[],[f30,f114])).

fof(f114,plain,(
    ! [X3] :
      ( sK3 = sK4(k3_xboole_0(sK1,sK2),X3)
      | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X3) ) ),
    inference(resolution,[],[f111,f24])).

fof(f111,plain,(
    ! [X0] :
      ( r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | sK3 = sK4(k3_xboole_0(sK1,sK2),X0) ) ),
    inference(resolution,[],[f109,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f109,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
      | sK3 = X0 ) ),
    inference(superposition,[],[f64,f51])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f219,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X4,X3))
      | k3_xboole_0(X4,X3) = X3 ) ),
    inference(resolution,[],[f204,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f204,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f87,f30])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f73,f29])).

fof(f4356,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f4149,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4149,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f4103,f22])).

fof(f4103,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK1)) ),
    inference(duplicate_literal_removal,[],[f4054])).

fof(f4054,plain,(
    ! [X0] :
      ( r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK1))
      | r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK1)) ) ),
    inference(resolution,[],[f3370,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f74,f29])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3370,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1)),X20)
      | r1_tarski(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f3300])).

fof(f3300,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(sK4(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1)),X20)
      | r1_tarski(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1))
      | r1_tarski(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1)) ) ),
    inference(resolution,[],[f115,f242])).

fof(f242,plain,(
    ! [X19,X20] :
      ( r2_hidden(sK4(k3_xboole_0(X19,sK0),X20),sK1)
      | r1_tarski(k3_xboole_0(X19,sK0),X20) ) ),
    inference(resolution,[],[f205,f29])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f203,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f203,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(X2,sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X2] :
      ( r1_tarski(k3_xboole_0(X2,sK0),sK1)
      | r1_tarski(k3_xboole_0(X2,sK0),sK1) ) ),
    inference(resolution,[],[f87,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK1),sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f91,f30])).

fof(f91,plain,(
    ! [X8] :
      ( r2_hidden(X8,sK1)
      | ~ r2_hidden(X8,sK0) ) ),
    inference(superposition,[],[f73,f82])).

fof(f82,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,k3_xboole_0(X1,X2)),X2)
      | ~ r2_hidden(sK4(X0,k3_xboole_0(X1,X2)),X1)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f72,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n003.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 09:32:57 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.22/0.52  % (13184)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (13206)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (13189)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (13201)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (13188)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (13208)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (13197)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (13198)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (13205)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (13193)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (13185)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (13183)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (13195)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (13186)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (13209)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (13207)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (13203)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (13192)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (13210)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (13211)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (13200)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (13194)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (13191)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (13190)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (13187)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (13202)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.59  % (13199)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (13213)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (13212)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.77/0.61  % (13204)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.77/0.61  % (13204)Refutation not found, incomplete strategy% (13204)------------------------------
% 1.77/0.61  % (13204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (13204)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.61  
% 1.77/0.61  % (13204)Memory used [KB]: 10746
% 1.77/0.61  % (13204)Time elapsed: 0.178 s
% 1.77/0.61  % (13204)------------------------------
% 1.77/0.61  % (13204)------------------------------
% 2.56/0.73  % (13189)Refutation found. Thanks to Tanya!
% 2.56/0.73  % SZS status Theorem for theBenchmark
% 2.56/0.73  % (13249)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.56/0.73  % SZS output start Proof for theBenchmark
% 2.56/0.73  fof(f4420,plain,(
% 2.56/0.73    $false),
% 2.56/0.73    inference(resolution,[],[f4356,f2725])).
% 2.56/0.73  fof(f2725,plain,(
% 2.56/0.73    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 2.56/0.73    inference(subsumption_resolution,[],[f2718,f78])).
% 2.56/0.73  fof(f78,plain,(
% 2.56/0.73    k3_xboole_0(sK1,sK2) != k3_xboole_0(sK0,sK2)),
% 2.56/0.73    inference(superposition,[],[f50,f51])).
% 2.56/0.73  fof(f51,plain,(
% 2.56/0.73    k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 2.56/0.73    inference(definition_unfolding,[],[f18,f49])).
% 2.56/0.73  fof(f49,plain,(
% 2.56/0.73    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.56/0.73    inference(definition_unfolding,[],[f21,f48])).
% 2.56/0.73  fof(f48,plain,(
% 2.56/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.56/0.73    inference(definition_unfolding,[],[f23,f35])).
% 2.56/0.73  fof(f35,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.56/0.73    inference(cnf_transformation,[],[f10])).
% 2.56/0.73  fof(f10,axiom,(
% 2.56/0.73    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.56/0.73  fof(f23,plain,(
% 2.56/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.56/0.73    inference(cnf_transformation,[],[f9])).
% 2.56/0.73  fof(f9,axiom,(
% 2.56/0.73    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.56/0.73  fof(f21,plain,(
% 2.56/0.73    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.56/0.73    inference(cnf_transformation,[],[f8])).
% 2.56/0.73  fof(f8,axiom,(
% 2.56/0.73    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.56/0.73  fof(f18,plain,(
% 2.56/0.73    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 2.56/0.73    inference(cnf_transformation,[],[f14])).
% 2.56/0.73  fof(f14,plain,(
% 2.56/0.73    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 2.56/0.73    inference(flattening,[],[f13])).
% 2.56/0.73  fof(f13,plain,(
% 2.56/0.73    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 2.56/0.73    inference(ennf_transformation,[],[f12])).
% 2.56/0.73  fof(f12,negated_conjecture,(
% 2.56/0.73    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.56/0.73    inference(negated_conjecture,[],[f11])).
% 2.56/0.73  fof(f11,conjecture,(
% 2.56/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 2.56/0.73  fof(f50,plain,(
% 2.56/0.73    k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 2.56/0.73    inference(definition_unfolding,[],[f20,f49])).
% 2.56/0.73  fof(f20,plain,(
% 2.56/0.73    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 2.56/0.73    inference(cnf_transformation,[],[f14])).
% 2.56/0.73  fof(f2718,plain,(
% 2.56/0.73    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,sK2)),
% 2.56/0.73    inference(superposition,[],[f219,f2671])).
% 2.56/0.73  fof(f2671,plain,(
% 2.56/0.73    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK2))),
% 2.56/0.73    inference(resolution,[],[f2640,f86])).
% 2.56/0.73  fof(f86,plain,(
% 2.56/0.73    r2_hidden(sK3,sK2)),
% 2.56/0.73    inference(resolution,[],[f73,f79])).
% 2.56/0.73  fof(f79,plain,(
% 2.56/0.73    r2_hidden(sK3,k3_xboole_0(sK1,sK2))),
% 2.56/0.73    inference(superposition,[],[f66,f51])).
% 2.56/0.73  fof(f66,plain,(
% 2.56/0.73    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 2.56/0.73    inference(equality_resolution,[],[f65])).
% 2.56/0.73  fof(f65,plain,(
% 2.56/0.73    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 2.56/0.73    inference(equality_resolution,[],[f55])).
% 2.56/0.73  fof(f55,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.56/0.73    inference(definition_unfolding,[],[f31,f49])).
% 2.56/0.73  fof(f31,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.56/0.73    inference(cnf_transformation,[],[f6])).
% 2.56/0.73  fof(f6,axiom,(
% 2.56/0.73    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.56/0.73  fof(f73,plain,(
% 2.56/0.73    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 2.56/0.73    inference(equality_resolution,[],[f46])).
% 2.56/0.73  fof(f46,plain,(
% 2.56/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.56/0.73    inference(cnf_transformation,[],[f3])).
% 2.56/0.73  fof(f3,axiom,(
% 2.56/0.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.56/0.73  fof(f2640,plain,(
% 2.56/0.73    ( ! [X65] : (~r2_hidden(sK3,X65) | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,X65))) )),
% 2.56/0.73    inference(resolution,[],[f549,f19])).
% 2.56/0.73  fof(f19,plain,(
% 2.56/0.73    r2_hidden(sK3,sK0)),
% 2.56/0.73    inference(cnf_transformation,[],[f14])).
% 2.56/0.73  fof(f549,plain,(
% 2.56/0.73    ( ! [X19,X20] : (~r2_hidden(sK3,X19) | ~r2_hidden(sK3,X20) | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X19,X20))) )),
% 2.56/0.73    inference(resolution,[],[f533,f72])).
% 2.56/0.73  fof(f72,plain,(
% 2.56/0.73    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_xboole_0(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 2.56/0.73    inference(equality_resolution,[],[f47])).
% 2.56/0.73  fof(f47,plain,(
% 2.56/0.73    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.56/0.73    inference(cnf_transformation,[],[f3])).
% 2.56/0.73  fof(f533,plain,(
% 2.56/0.73    ( ! [X3] : (~r2_hidden(sK3,X3) | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X3)) )),
% 2.56/0.73    inference(subsumption_resolution,[],[f530,f24])).
% 2.56/0.73  fof(f24,plain,(
% 2.56/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.56/0.73    inference(cnf_transformation,[],[f15])).
% 2.56/0.73  fof(f15,plain,(
% 2.56/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.56/0.73    inference(ennf_transformation,[],[f5])).
% 2.56/0.73  fof(f5,axiom,(
% 2.56/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.56/0.73  fof(f530,plain,(
% 2.56/0.73    ( ! [X3] : (~r2_hidden(sK3,X3) | r1_tarski(k3_xboole_0(sK1,sK2),X3) | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X3)) )),
% 2.56/0.73    inference(superposition,[],[f30,f114])).
% 2.56/0.73  fof(f114,plain,(
% 2.56/0.73    ( ! [X3] : (sK3 = sK4(k3_xboole_0(sK1,sK2),X3) | k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X3)) )),
% 2.56/0.73    inference(resolution,[],[f111,f24])).
% 2.56/0.73  fof(f111,plain,(
% 2.56/0.73    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,sK2),X0) | sK3 = sK4(k3_xboole_0(sK1,sK2),X0)) )),
% 2.56/0.73    inference(resolution,[],[f109,f29])).
% 2.56/0.73  fof(f29,plain,(
% 2.56/0.73    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.56/0.73    inference(cnf_transformation,[],[f16])).
% 2.56/0.73  fof(f16,plain,(
% 2.56/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.56/0.73    inference(ennf_transformation,[],[f2])).
% 2.56/0.73  fof(f2,axiom,(
% 2.56/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.56/0.73  fof(f109,plain,(
% 2.56/0.73    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2)) | sK3 = X0) )),
% 2.56/0.73    inference(superposition,[],[f64,f51])).
% 2.56/0.73  fof(f64,plain,(
% 2.56/0.73    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 2.56/0.73    inference(equality_resolution,[],[f54])).
% 2.56/0.73  fof(f54,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.56/0.73    inference(definition_unfolding,[],[f32,f49])).
% 2.56/0.73  fof(f32,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.56/0.73    inference(cnf_transformation,[],[f6])).
% 2.56/0.73  fof(f30,plain,(
% 2.56/0.73    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.56/0.73    inference(cnf_transformation,[],[f16])).
% 2.56/0.73  fof(f219,plain,(
% 2.56/0.73    ( ! [X4,X3] : (~r1_tarski(X3,k3_xboole_0(X4,X3)) | k3_xboole_0(X4,X3) = X3) )),
% 2.56/0.73    inference(resolution,[],[f204,f27])).
% 2.56/0.73  fof(f27,plain,(
% 2.56/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.56/0.73    inference(cnf_transformation,[],[f4])).
% 2.56/0.73  fof(f4,axiom,(
% 2.56/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.56/0.73  fof(f204,plain,(
% 2.56/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.56/0.73    inference(duplicate_literal_removal,[],[f189])).
% 2.56/0.73  fof(f189,plain,(
% 2.56/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.56/0.73    inference(resolution,[],[f87,f30])).
% 2.56/0.73  fof(f87,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.56/0.73    inference(resolution,[],[f73,f29])).
% 2.56/0.73  fof(f4356,plain,(
% 2.56/0.73    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,X0))) )),
% 2.56/0.73    inference(superposition,[],[f4149,f22])).
% 2.56/0.73  fof(f22,plain,(
% 2.56/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.56/0.73    inference(cnf_transformation,[],[f1])).
% 2.56/0.73  fof(f1,axiom,(
% 2.56/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.56/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.56/0.73  fof(f4149,plain,(
% 2.56/0.73    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(X0,sK1))) )),
% 2.56/0.73    inference(superposition,[],[f4103,f22])).
% 2.56/0.73  fof(f4103,plain,(
% 2.56/0.73    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK1))) )),
% 2.56/0.73    inference(duplicate_literal_removal,[],[f4054])).
% 2.56/0.73  fof(f4054,plain,(
% 2.56/0.73    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK1)) | r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK1))) )),
% 2.56/0.73    inference(resolution,[],[f3370,f93])).
% 2.56/0.73  fof(f93,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.56/0.73    inference(resolution,[],[f74,f29])).
% 2.56/0.73  fof(f74,plain,(
% 2.56/0.73    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 2.56/0.73    inference(equality_resolution,[],[f45])).
% 2.56/0.73  fof(f45,plain,(
% 2.56/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.56/0.73    inference(cnf_transformation,[],[f3])).
% 2.56/0.73  fof(f3370,plain,(
% 2.56/0.73    ( ! [X19,X20] : (~r2_hidden(sK4(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1)),X20) | r1_tarski(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1))) )),
% 2.56/0.73    inference(duplicate_literal_removal,[],[f3300])).
% 2.56/0.73  fof(f3300,plain,(
% 2.56/0.73    ( ! [X19,X20] : (~r2_hidden(sK4(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1)),X20) | r1_tarski(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1)) | r1_tarski(k3_xboole_0(X19,sK0),k3_xboole_0(X20,sK1))) )),
% 2.56/0.73    inference(resolution,[],[f115,f242])).
% 2.56/0.73  fof(f242,plain,(
% 2.56/0.73    ( ! [X19,X20] : (r2_hidden(sK4(k3_xboole_0(X19,sK0),X20),sK1) | r1_tarski(k3_xboole_0(X19,sK0),X20)) )),
% 2.56/0.73    inference(resolution,[],[f205,f29])).
% 2.56/0.73  fof(f205,plain,(
% 2.56/0.73    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,sK0)) | r2_hidden(X0,sK1)) )),
% 2.56/0.73    inference(resolution,[],[f203,f28])).
% 2.56/0.73  fof(f28,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.56/0.73    inference(cnf_transformation,[],[f16])).
% 2.56/0.73  fof(f203,plain,(
% 2.56/0.73    ( ! [X2] : (r1_tarski(k3_xboole_0(X2,sK0),sK1)) )),
% 2.56/0.73    inference(duplicate_literal_removal,[],[f190])).
% 2.56/0.73  fof(f190,plain,(
% 2.56/0.73    ( ! [X2] : (r1_tarski(k3_xboole_0(X2,sK0),sK1) | r1_tarski(k3_xboole_0(X2,sK0),sK1)) )),
% 2.56/0.73    inference(resolution,[],[f87,f98])).
% 2.56/0.73  fof(f98,plain,(
% 2.56/0.73    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK0) | r1_tarski(X0,sK1)) )),
% 2.56/0.73    inference(resolution,[],[f91,f30])).
% 2.56/0.73  fof(f91,plain,(
% 2.56/0.73    ( ! [X8] : (r2_hidden(X8,sK1) | ~r2_hidden(X8,sK0)) )),
% 2.56/0.73    inference(superposition,[],[f73,f82])).
% 2.56/0.73  fof(f82,plain,(
% 2.56/0.73    sK0 = k3_xboole_0(sK0,sK1)),
% 2.56/0.73    inference(resolution,[],[f24,f17])).
% 2.56/0.73  fof(f17,plain,(
% 2.56/0.73    r1_tarski(sK0,sK1)),
% 2.56/0.73    inference(cnf_transformation,[],[f14])).
% 2.56/0.73  fof(f115,plain,(
% 2.56/0.73    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,k3_xboole_0(X1,X2)),X2) | ~r2_hidden(sK4(X0,k3_xboole_0(X1,X2)),X1) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 2.56/0.73    inference(resolution,[],[f72,f30])).
% 2.56/0.73  % SZS output end Proof for theBenchmark
% 2.56/0.73  % (13189)------------------------------
% 2.56/0.73  % (13189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.56/0.73  % (13189)Termination reason: Refutation
% 2.56/0.73  
% 2.56/0.73  % (13189)Memory used [KB]: 9210
% 2.56/0.73  % (13189)Time elapsed: 0.200 s
% 2.56/0.74  % (13189)------------------------------
% 2.56/0.74  % (13189)------------------------------
% 2.56/0.74  % (13174)Success in time 0.36 s
%------------------------------------------------------------------------------

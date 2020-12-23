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
% DateTime   : Thu Dec  3 12:43:04 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 161 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  122 ( 241 expanded)
%              Number of equality atoms :   52 ( 139 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1224,f64])).

fof(f64,plain,(
    sK2 != k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f1224,plain,(
    sK2 = k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1201,f551])).

fof(f551,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f546,f380])).

fof(f380,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f247,f66])).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f46,f49,f49])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f247,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f67,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f67,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f546,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X3)) ),
    inference(superposition,[],[f537,f68])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f537,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f530,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f530,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f522,f67])).

fof(f522,plain,(
    ! [X2,X1] : k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f68,f265])).

fof(f265,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f250,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f250,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f248,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f248,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f65,f67])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1201,plain,(
    k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f946,f725])).

fof(f725,plain,(
    k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f714,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f714,plain,(
    r1_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f39,f40,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f49])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f40,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f946,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f915,f247])).

fof(f915,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(superposition,[],[f69,f249])).

fof(f249,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f248,f56])).

fof(f69,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (17039)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (17032)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (17038)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (17035)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (17048)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (17047)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (17048)Refutation not found, incomplete strategy% (17048)------------------------------
% 0.22/0.53  % (17048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17048)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17048)Memory used [KB]: 10746
% 0.22/0.53  % (17048)Time elapsed: 0.101 s
% 0.22/0.53  % (17048)------------------------------
% 0.22/0.53  % (17048)------------------------------
% 0.22/0.53  % (17054)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (17055)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (17031)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (17028)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (17028)Refutation not found, incomplete strategy% (17028)------------------------------
% 0.22/0.54  % (17028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17028)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17028)Memory used [KB]: 10746
% 0.22/0.54  % (17028)Time elapsed: 0.125 s
% 0.22/0.54  % (17028)------------------------------
% 0.22/0.54  % (17028)------------------------------
% 0.22/0.54  % (17026)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (17026)Refutation not found, incomplete strategy% (17026)------------------------------
% 0.22/0.54  % (17026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17026)Memory used [KB]: 1663
% 0.22/0.54  % (17026)Time elapsed: 0.133 s
% 0.22/0.54  % (17026)------------------------------
% 0.22/0.54  % (17026)------------------------------
% 0.22/0.54  % (17029)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (17037)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (17030)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (17050)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (17037)Refutation not found, incomplete strategy% (17037)------------------------------
% 0.22/0.54  % (17037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17051)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (17027)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (17041)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (17035)Refutation not found, incomplete strategy% (17035)------------------------------
% 0.22/0.55  % (17035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17035)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17035)Memory used [KB]: 10618
% 0.22/0.55  % (17035)Time elapsed: 0.121 s
% 0.22/0.55  % (17035)------------------------------
% 0.22/0.55  % (17035)------------------------------
% 0.22/0.55  % (17046)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (17044)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (17043)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (17033)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (17043)Refutation not found, incomplete strategy% (17043)------------------------------
% 0.22/0.55  % (17043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17043)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17043)Memory used [KB]: 10618
% 0.22/0.55  % (17043)Time elapsed: 0.136 s
% 0.22/0.55  % (17043)------------------------------
% 0.22/0.55  % (17043)------------------------------
% 0.22/0.55  % (17037)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17037)Memory used [KB]: 10618
% 0.22/0.55  % (17037)Time elapsed: 0.134 s
% 0.22/0.55  % (17037)------------------------------
% 0.22/0.55  % (17037)------------------------------
% 0.22/0.55  % (17049)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (17036)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (17034)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (17036)Refutation not found, incomplete strategy% (17036)------------------------------
% 0.22/0.55  % (17036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17036)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17036)Memory used [KB]: 10618
% 0.22/0.55  % (17036)Time elapsed: 0.149 s
% 0.22/0.55  % (17036)------------------------------
% 0.22/0.55  % (17036)------------------------------
% 0.22/0.55  % (17034)Refutation not found, incomplete strategy% (17034)------------------------------
% 0.22/0.55  % (17034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17034)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17034)Memory used [KB]: 10746
% 0.22/0.55  % (17034)Time elapsed: 0.148 s
% 0.22/0.55  % (17034)------------------------------
% 0.22/0.55  % (17034)------------------------------
% 0.22/0.55  % (17040)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (17042)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (17053)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (17052)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (17045)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.16/0.65  % (17111)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.16/0.68  % (17115)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.16/0.68  % (17106)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.16/0.68  % (17114)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.16/0.68  % (17116)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.16/0.68  % (17107)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.16/0.69  % (17121)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.16/0.70  % (17106)Refutation not found, incomplete strategy% (17106)------------------------------
% 2.16/0.70  % (17106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (17106)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (17106)Memory used [KB]: 6140
% 2.16/0.70  % (17106)Time elapsed: 0.128 s
% 2.16/0.70  % (17106)------------------------------
% 2.16/0.70  % (17106)------------------------------
% 2.70/0.71  % (17118)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.70/0.76  % (17121)Refutation found. Thanks to Tanya!
% 2.70/0.76  % SZS status Theorem for theBenchmark
% 2.70/0.76  % SZS output start Proof for theBenchmark
% 2.70/0.76  fof(f1225,plain,(
% 2.70/0.76    $false),
% 2.70/0.76    inference(subsumption_resolution,[],[f1224,f64])).
% 2.70/0.76  fof(f64,plain,(
% 2.70/0.76    sK2 != k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))),
% 2.70/0.76    inference(definition_unfolding,[],[f41,f49])).
% 2.70/0.76  fof(f49,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f17])).
% 2.70/0.76  fof(f17,axiom,(
% 2.70/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.70/0.76  fof(f41,plain,(
% 2.70/0.76    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.70/0.76    inference(cnf_transformation,[],[f33])).
% 2.70/0.76  fof(f33,plain,(
% 2.70/0.76    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 2.70/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f32])).
% 2.70/0.76  fof(f32,plain,(
% 2.70/0.76    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 2.70/0.76    introduced(choice_axiom,[])).
% 2.70/0.76  fof(f24,plain,(
% 2.70/0.76    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.70/0.76    inference(ennf_transformation,[],[f21])).
% 2.70/0.76  fof(f21,negated_conjecture,(
% 2.70/0.76    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.70/0.76    inference(negated_conjecture,[],[f20])).
% 2.70/0.76  fof(f20,conjecture,(
% 2.70/0.76    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 2.70/0.76  fof(f1224,plain,(
% 2.70/0.76    sK2 = k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))),
% 2.70/0.76    inference(forward_demodulation,[],[f1201,f551])).
% 2.70/0.76  fof(f551,plain,(
% 2.70/0.76    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 2.70/0.76    inference(forward_demodulation,[],[f546,f380])).
% 2.70/0.76  fof(f380,plain,(
% 2.70/0.76    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 2.70/0.76    inference(superposition,[],[f247,f66])).
% 2.70/0.76  fof(f66,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.70/0.76    inference(definition_unfolding,[],[f46,f49,f49])).
% 2.70/0.76  fof(f46,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f16])).
% 2.70/0.76  fof(f16,axiom,(
% 2.70/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.70/0.76  fof(f247,plain,(
% 2.70/0.76    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 2.70/0.76    inference(superposition,[],[f67,f42])).
% 2.70/0.76  fof(f42,plain,(
% 2.70/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f9])).
% 2.70/0.76  fof(f9,axiom,(
% 2.70/0.76    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.70/0.76  fof(f67,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 2.70/0.76    inference(definition_unfolding,[],[f48,f63])).
% 2.70/0.76  fof(f63,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.70/0.76    inference(definition_unfolding,[],[f50,f49])).
% 2.70/0.76  fof(f50,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f19])).
% 2.70/0.76  fof(f19,axiom,(
% 2.70/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 2.70/0.76  fof(f48,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.70/0.76    inference(cnf_transformation,[],[f8])).
% 2.70/0.76  fof(f8,axiom,(
% 2.70/0.76    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.70/0.76  fof(f546,plain,(
% 2.70/0.76    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X3))) )),
% 2.70/0.76    inference(superposition,[],[f537,f68])).
% 2.70/0.76  fof(f68,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.70/0.76    inference(definition_unfolding,[],[f51,f63])).
% 2.70/0.76  fof(f51,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f14])).
% 2.70/0.76  fof(f14,axiom,(
% 2.70/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.70/0.76  fof(f537,plain,(
% 2.70/0.76    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.70/0.76    inference(superposition,[],[f530,f47])).
% 2.70/0.76  fof(f47,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f1])).
% 2.70/0.76  fof(f1,axiom,(
% 2.70/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.70/0.76  fof(f530,plain,(
% 2.70/0.76    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.70/0.76    inference(forward_demodulation,[],[f522,f67])).
% 2.70/0.76  fof(f522,plain,(
% 2.70/0.76    ( ! [X2,X1] : (k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k1_xboole_0)) )),
% 2.70/0.76    inference(superposition,[],[f68,f265])).
% 2.70/0.76  fof(f265,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.70/0.76    inference(unit_resulting_resolution,[],[f250,f56])).
% 2.70/0.76  fof(f56,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f38])).
% 2.70/0.76  fof(f38,plain,(
% 2.70/0.76    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.70/0.76    inference(nnf_transformation,[],[f5])).
% 2.70/0.76  fof(f5,axiom,(
% 2.70/0.76    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.70/0.76  fof(f250,plain,(
% 2.70/0.76    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.70/0.76    inference(unit_resulting_resolution,[],[f248,f61])).
% 2.70/0.76  fof(f61,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f30])).
% 2.70/0.76  fof(f30,plain,(
% 2.70/0.76    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.70/0.76    inference(ennf_transformation,[],[f7])).
% 2.70/0.76  fof(f7,axiom,(
% 2.70/0.76    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.70/0.76  fof(f248,plain,(
% 2.70/0.76    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.70/0.76    inference(superposition,[],[f65,f67])).
% 2.70/0.76  fof(f65,plain,(
% 2.70/0.76    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.70/0.76    inference(definition_unfolding,[],[f44,f63])).
% 2.70/0.76  fof(f44,plain,(
% 2.70/0.76    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f12])).
% 2.70/0.76  fof(f12,axiom,(
% 2.70/0.76    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.70/0.76  fof(f1201,plain,(
% 2.70/0.76    k4_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.70/0.76    inference(superposition,[],[f946,f725])).
% 2.70/0.76  fof(f725,plain,(
% 2.70/0.76    k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 2.70/0.76    inference(unit_resulting_resolution,[],[f714,f72])).
% 2.70/0.76  fof(f72,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.70/0.76    inference(resolution,[],[f53,f43])).
% 2.70/0.76  fof(f43,plain,(
% 2.70/0.76    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.70/0.76    inference(cnf_transformation,[],[f35])).
% 2.70/0.76  fof(f35,plain,(
% 2.70/0.76    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.70/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f34])).
% 2.70/0.76  fof(f34,plain,(
% 2.70/0.76    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.70/0.76    introduced(choice_axiom,[])).
% 2.70/0.76  fof(f25,plain,(
% 2.70/0.76    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.70/0.76    inference(ennf_transformation,[],[f4])).
% 2.70/0.76  fof(f4,axiom,(
% 2.70/0.76    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.70/0.76  fof(f53,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f37])).
% 2.70/0.76  fof(f37,plain,(
% 2.70/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.70/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f36])).
% 2.70/0.76  fof(f36,plain,(
% 2.70/0.76    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.70/0.76    introduced(choice_axiom,[])).
% 2.70/0.76  fof(f26,plain,(
% 2.70/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.70/0.76    inference(ennf_transformation,[],[f22])).
% 2.70/0.76  fof(f22,plain,(
% 2.70/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.70/0.76    inference(rectify,[],[f3])).
% 2.70/0.76  fof(f3,axiom,(
% 2.70/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.70/0.76  fof(f714,plain,(
% 2.70/0.76    r1_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 2.70/0.76    inference(unit_resulting_resolution,[],[f39,f40,f71])).
% 2.70/0.76  fof(f71,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.70/0.76    inference(definition_unfolding,[],[f62,f49])).
% 2.70/0.76  fof(f62,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f31])).
% 2.70/0.76  fof(f31,plain,(
% 2.70/0.76    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 2.70/0.76    inference(ennf_transformation,[],[f18])).
% 2.70/0.76  fof(f18,axiom,(
% 2.70/0.76    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 2.70/0.76  fof(f40,plain,(
% 2.70/0.76    ~r2_hidden(sK1,sK2)),
% 2.70/0.76    inference(cnf_transformation,[],[f33])).
% 2.70/0.76  fof(f39,plain,(
% 2.70/0.76    ~r2_hidden(sK0,sK2)),
% 2.70/0.76    inference(cnf_transformation,[],[f33])).
% 2.70/0.76  fof(f946,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f915,f247])).
% 2.70/0.76  fof(f915,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k1_xboole_0))) )),
% 2.70/0.76    inference(superposition,[],[f69,f249])).
% 2.70/0.76  fof(f249,plain,(
% 2.70/0.76    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.70/0.76    inference(unit_resulting_resolution,[],[f248,f56])).
% 2.70/0.76  fof(f69,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 2.70/0.76    inference(definition_unfolding,[],[f59,f63])).
% 2.70/0.76  fof(f59,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f6])).
% 2.70/0.76  fof(f6,axiom,(
% 2.70/0.76    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 2.70/0.76  % SZS output end Proof for theBenchmark
% 2.70/0.76  % (17121)------------------------------
% 2.70/0.76  % (17121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.76  % (17121)Termination reason: Refutation
% 2.70/0.76  
% 2.70/0.76  % (17121)Memory used [KB]: 6652
% 2.70/0.76  % (17121)Time elapsed: 0.182 s
% 2.70/0.76  % (17121)------------------------------
% 2.70/0.76  % (17121)------------------------------
% 2.70/0.76  % (17022)Success in time 0.397 s
%------------------------------------------------------------------------------

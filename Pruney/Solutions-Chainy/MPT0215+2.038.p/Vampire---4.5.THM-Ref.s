%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:13 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 130 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 148 expanded)
%              Number of equality atoms :   50 ( 136 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f111,f51])).

fof(f51,plain,(
    ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f27,f41,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f111,plain,(
    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f59,f43])).

fof(f43,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(definition_unfolding,[],[f20,f41,f40])).

fof(f20,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f48,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f34,f35,f37,f37])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f48,plain,(
    ! [X2,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) ),
    inference(superposition,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f28,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (18957)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (18957)Refutation not found, incomplete strategy% (18957)------------------------------
% 0.20/0.53  % (18957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18957)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18957)Memory used [KB]: 10618
% 0.20/0.53  % (18957)Time elapsed: 0.121 s
% 0.20/0.53  % (18957)------------------------------
% 0.20/0.53  % (18957)------------------------------
% 0.20/0.53  % (18973)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (18973)Refutation not found, incomplete strategy% (18973)------------------------------
% 0.20/0.53  % (18973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18964)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (18973)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18973)Memory used [KB]: 6140
% 0.20/0.53  % (18973)Time elapsed: 0.124 s
% 0.20/0.53  % (18973)------------------------------
% 0.20/0.53  % (18973)------------------------------
% 0.20/0.53  % (18964)Refutation not found, incomplete strategy% (18964)------------------------------
% 0.20/0.53  % (18964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18964)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18964)Memory used [KB]: 1663
% 0.20/0.53  % (18964)Time elapsed: 0.122 s
% 0.20/0.53  % (18964)------------------------------
% 0.20/0.53  % (18964)------------------------------
% 0.20/0.56  % (18970)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (18948)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.56  % (18947)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.56  % (18946)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.56  % (18950)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.56  % (18946)Refutation not found, incomplete strategy% (18946)------------------------------
% 0.20/0.56  % (18946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18946)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18946)Memory used [KB]: 1663
% 0.20/0.56  % (18946)Time elapsed: 0.146 s
% 0.20/0.56  % (18946)------------------------------
% 0.20/0.56  % (18946)------------------------------
% 0.20/0.56  % (18945)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.57/0.57  % (18949)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.57  % (18955)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.57/0.57  % (18952)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.57  % (18961)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.57  % (18961)Refutation not found, incomplete strategy% (18961)------------------------------
% 1.57/0.57  % (18961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (18961)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (18961)Memory used [KB]: 10618
% 1.57/0.57  % (18961)Time elapsed: 0.157 s
% 1.57/0.57  % (18961)------------------------------
% 1.57/0.57  % (18961)------------------------------
% 1.57/0.57  % (18971)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.57  % (18958)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.57/0.57  % (18971)Refutation not found, incomplete strategy% (18971)------------------------------
% 1.57/0.57  % (18971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (18971)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (18971)Memory used [KB]: 6140
% 1.57/0.57  % (18971)Time elapsed: 0.158 s
% 1.57/0.57  % (18971)------------------------------
% 1.57/0.57  % (18971)------------------------------
% 1.57/0.57  % (18962)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.57/0.57  % (18953)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.57/0.57  % (18962)Refutation not found, incomplete strategy% (18962)------------------------------
% 1.57/0.57  % (18962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (18962)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (18962)Memory used [KB]: 1663
% 1.57/0.57  % (18962)Time elapsed: 0.152 s
% 1.57/0.57  % (18962)------------------------------
% 1.57/0.57  % (18962)------------------------------
% 1.57/0.57  % (18965)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.57/0.58  % (18974)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.58  % (18969)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.58  % (18970)Refutation not found, incomplete strategy% (18970)------------------------------
% 1.57/0.58  % (18970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (18970)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (18970)Memory used [KB]: 10618
% 1.57/0.58  % (18970)Time elapsed: 0.170 s
% 1.57/0.58  % (18970)------------------------------
% 1.57/0.58  % (18970)------------------------------
% 1.57/0.58  % (18955)Refutation not found, incomplete strategy% (18955)------------------------------
% 1.57/0.58  % (18955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (18955)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (18955)Memory used [KB]: 10746
% 1.57/0.58  % (18955)Time elapsed: 0.166 s
% 1.57/0.58  % (18955)------------------------------
% 1.57/0.58  % (18955)------------------------------
% 1.57/0.58  % (18960)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.58  % (18975)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.58  % (18975)Refutation not found, incomplete strategy% (18975)------------------------------
% 1.57/0.58  % (18975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (18975)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (18975)Memory used [KB]: 1663
% 1.57/0.58  % (18975)Time elapsed: 0.001 s
% 1.57/0.58  % (18975)------------------------------
% 1.57/0.58  % (18975)------------------------------
% 1.57/0.58  % (18974)Refutation not found, incomplete strategy% (18974)------------------------------
% 1.57/0.58  % (18974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (18972)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.59  % (18974)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (18974)Memory used [KB]: 10746
% 1.57/0.59  % (18974)Time elapsed: 0.164 s
% 1.57/0.59  % (18974)------------------------------
% 1.57/0.59  % (18974)------------------------------
% 1.57/0.59  % (18972)Refutation not found, incomplete strategy% (18972)------------------------------
% 1.57/0.59  % (18972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (18972)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (18972)Memory used [KB]: 6140
% 1.57/0.59  % (18972)Time elapsed: 0.180 s
% 1.57/0.59  % (18972)------------------------------
% 1.57/0.59  % (18972)------------------------------
% 1.75/0.59  % (18949)Refutation found. Thanks to Tanya!
% 1.75/0.59  % SZS status Theorem for theBenchmark
% 1.75/0.59  % SZS output start Proof for theBenchmark
% 1.75/0.59  fof(f118,plain,(
% 1.75/0.59    $false),
% 1.75/0.59    inference(subsumption_resolution,[],[f111,f51])).
% 1.75/0.59  fof(f51,plain,(
% 1.75/0.59    ~r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f21,f45])).
% 1.75/0.59  fof(f45,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 1.75/0.59    inference(definition_unfolding,[],[f27,f41,f41])).
% 1.75/0.59  fof(f41,plain,(
% 1.75/0.59    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f22,f40])).
% 1.75/0.59  fof(f40,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f24,f39])).
% 1.75/0.59  fof(f39,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f29,f37])).
% 1.75/0.59  fof(f37,plain,(
% 1.75/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f30,f36])).
% 1.75/0.59  fof(f36,plain,(
% 1.75/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f31,f32])).
% 1.75/0.59  fof(f32,plain,(
% 1.75/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f11])).
% 1.75/0.59  fof(f11,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.75/0.59  fof(f31,plain,(
% 1.75/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f10])).
% 1.75/0.59  fof(f10,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.75/0.59  fof(f30,plain,(
% 1.75/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f9])).
% 1.75/0.59  fof(f9,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.75/0.59  fof(f29,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f8])).
% 1.75/0.59  fof(f8,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.75/0.59  fof(f24,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f7])).
% 1.75/0.59  fof(f7,axiom,(
% 1.75/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.75/0.59  fof(f22,plain,(
% 1.75/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f6])).
% 1.75/0.59  fof(f6,axiom,(
% 1.75/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.75/0.59  fof(f27,plain,(
% 1.75/0.59    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f17])).
% 1.75/0.59  fof(f17,plain,(
% 1.75/0.59    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.75/0.59    inference(ennf_transformation,[],[f13])).
% 1.75/0.59  fof(f13,axiom,(
% 1.75/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.75/0.59  fof(f21,plain,(
% 1.75/0.59    sK0 != sK1),
% 1.75/0.59    inference(cnf_transformation,[],[f19])).
% 1.75/0.59  fof(f19,plain,(
% 1.75/0.59    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 1.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 1.75/0.59  fof(f18,plain,(
% 1.75/0.59    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f16,plain,(
% 1.75/0.59    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 1.75/0.59    inference(ennf_transformation,[],[f15])).
% 1.75/0.59  fof(f15,negated_conjecture,(
% 1.75/0.59    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 1.75/0.59    inference(negated_conjecture,[],[f14])).
% 1.75/0.59  fof(f14,conjecture,(
% 1.75/0.59    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 1.75/0.59  fof(f111,plain,(
% 1.75/0.59    r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.75/0.59    inference(superposition,[],[f59,f43])).
% 1.75/0.59  fof(f43,plain,(
% 1.75/0.59    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.75/0.59    inference(definition_unfolding,[],[f20,f41,f40])).
% 1.75/0.59  fof(f20,plain,(
% 1.75/0.59    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 1.75/0.59    inference(cnf_transformation,[],[f19])).
% 1.75/0.59  fof(f59,plain,(
% 1.75/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 1.75/0.59    inference(superposition,[],[f48,f42])).
% 1.75/0.59  fof(f42,plain,(
% 1.75/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))))) )),
% 1.75/0.59    inference(definition_unfolding,[],[f33,f38])).
% 1.75/0.59  fof(f38,plain,(
% 1.75/0.59    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 1.75/0.59    inference(definition_unfolding,[],[f34,f35,f37,f37])).
% 1.75/0.59  fof(f35,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.75/0.59    inference(definition_unfolding,[],[f26,f25])).
% 1.75/0.59  fof(f25,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f1])).
% 1.75/0.59  fof(f1,axiom,(
% 1.75/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.75/0.59  fof(f26,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f4])).
% 1.75/0.59  fof(f4,axiom,(
% 1.75/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.75/0.59  fof(f34,plain,(
% 1.75/0.59    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f5])).
% 1.75/0.59  fof(f5,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 1.75/0.59  fof(f33,plain,(
% 1.75/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f12])).
% 1.75/0.59  fof(f12,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.75/0.59  fof(f48,plain,(
% 1.75/0.59    ( ! [X2,X0] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))) )),
% 1.75/0.59    inference(superposition,[],[f46,f44])).
% 1.75/0.59  fof(f44,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.75/0.59    inference(definition_unfolding,[],[f23,f35])).
% 1.75/0.59  fof(f23,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.75/0.59    inference(cnf_transformation,[],[f2])).
% 1.75/0.59  fof(f2,axiom,(
% 1.75/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.75/0.59  fof(f46,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))) )),
% 1.75/0.59    inference(definition_unfolding,[],[f28,f35])).
% 1.75/0.59  fof(f28,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f3])).
% 1.75/0.59  fof(f3,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 1.75/0.59  % SZS output end Proof for theBenchmark
% 1.75/0.59  % (18949)------------------------------
% 1.75/0.59  % (18949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (18949)Termination reason: Refutation
% 1.75/0.59  
% 1.75/0.59  % (18949)Memory used [KB]: 1791
% 1.75/0.59  % (18949)Time elapsed: 0.162 s
% 1.75/0.59  % (18949)------------------------------
% 1.75/0.59  % (18949)------------------------------
% 1.75/0.59  % (18944)Success in time 0.223 s
%------------------------------------------------------------------------------

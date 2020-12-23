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
% DateTime   : Thu Dec  3 12:36:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 144 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 217 expanded)
%              Number of equality atoms :   58 ( 154 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f500,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f499])).

fof(f499,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f152,f444])).

fof(f444,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(trivial_inequality_removal,[],[f442])).

fof(f442,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k4_xboole_0(X0,k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f282,f124])).

fof(f124,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f123,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f123,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f108,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f108,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f53,f37])).

fof(f282,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0)
      | k4_xboole_0(X0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f103,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    ! [X7] :
      ( ~ r1_tarski(k4_xboole_0(X7,k1_xboole_0),X7)
      | k4_xboole_0(X7,k1_xboole_0) = X7 ) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,(
    ! [X7] :
      ( k1_xboole_0 != k1_xboole_0
      | k4_xboole_0(X7,k1_xboole_0) = X7
      | ~ r1_tarski(k4_xboole_0(X7,k1_xboole_0),X7) ) ),
    inference(superposition,[],[f45,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f38,f42])).

fof(f45,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X2)
      | X1 = X2
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f31,f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f152,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f36,f80])).

fof(f80,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X5)) ),
    inference(resolution,[],[f39,f27])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f36,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f35,f22,f35,f34])).

fof(f19,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (11988)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (12002)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (11993)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (11996)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (12002)Refutation not found, incomplete strategy% (12002)------------------------------
% 0.22/0.52  % (12002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12002)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12002)Memory used [KB]: 1663
% 0.22/0.52  % (12002)Time elapsed: 0.095 s
% 0.22/0.52  % (12002)------------------------------
% 0.22/0.52  % (12002)------------------------------
% 0.22/0.52  % (11997)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (11995)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (12010)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (11999)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (12006)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (11992)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (11990)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (11991)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (12006)Refutation not found, incomplete strategy% (12006)------------------------------
% 0.22/0.53  % (12006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12006)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12006)Memory used [KB]: 1663
% 0.22/0.53  % (12006)Time elapsed: 0.118 s
% 0.22/0.53  % (12006)------------------------------
% 0.22/0.53  % (12006)------------------------------
% 0.22/0.54  % (11989)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (12009)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (11989)Refutation not found, incomplete strategy% (11989)------------------------------
% 0.22/0.54  % (11989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11989)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11989)Memory used [KB]: 1663
% 0.22/0.54  % (11989)Time elapsed: 0.127 s
% 0.22/0.54  % (11989)------------------------------
% 0.22/0.54  % (11989)------------------------------
% 0.22/0.54  % (11999)Refutation not found, incomplete strategy% (11999)------------------------------
% 0.22/0.54  % (11999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11999)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11999)Memory used [KB]: 6140
% 0.22/0.54  % (11999)Time elapsed: 0.128 s
% 0.22/0.54  % (11999)------------------------------
% 0.22/0.54  % (11999)------------------------------
% 0.22/0.54  % (11998)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (11993)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f500,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f499])).
% 0.22/0.54  fof(f499,plain,(
% 0.22/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(superposition,[],[f152,f444])).
% 0.22/0.54  fof(f444,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f442])).
% 0.22/0.54  fof(f442,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(superposition,[],[f282,f124])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f123,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f27,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f108,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.54    inference(superposition,[],[f38,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f20,f22,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f21,f22])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) )),
% 0.22/0.54    inference(superposition,[],[f53,f37])).
% 0.22/0.54  fof(f282,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0) | k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(resolution,[],[f103,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X7] : (~r1_tarski(k4_xboole_0(X7,k1_xboole_0),X7) | k4_xboole_0(X7,k1_xboole_0) = X7) )),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X7] : (k1_xboole_0 != k1_xboole_0 | k4_xboole_0(X7,k1_xboole_0) = X7 | ~r1_tarski(k4_xboole_0(X7,k1_xboole_0),X7)) )),
% 0.22/0.54    inference(superposition,[],[f45,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.54    inference(superposition,[],[f38,f42])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k1_xboole_0 != k4_xboole_0(X1,X2) | X1 = X2 | ~r1_tarski(X2,X1)) )),
% 0.22/0.54    inference(resolution,[],[f31,f26])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 0.22/0.54    inference(backward_demodulation,[],[f36,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X5))) )),
% 0.22/0.54    inference(resolution,[],[f39,f27])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f24,f35,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f23,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f25,f34])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.22/0.54    inference(definition_unfolding,[],[f19,f35,f22,f35,f34])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1] : k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (11993)------------------------------
% 0.22/0.54  % (11993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11993)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (11993)Memory used [KB]: 1918
% 0.22/0.54  % (11993)Time elapsed: 0.139 s
% 0.22/0.54  % (11993)------------------------------
% 0.22/0.54  % (11993)------------------------------
% 0.22/0.54  % (11998)Refutation not found, incomplete strategy% (11998)------------------------------
% 0.22/0.54  % (11998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11998)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11998)Memory used [KB]: 10618
% 0.22/0.54  % (11998)Time elapsed: 0.137 s
% 0.22/0.54  % (11998)------------------------------
% 0.22/0.54  % (11998)------------------------------
% 1.41/0.54  % (12016)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.54  % (12014)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.54  % (12016)Refutation not found, incomplete strategy% (12016)------------------------------
% 1.41/0.54  % (12016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (12016)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (12016)Memory used [KB]: 10618
% 1.41/0.54  % (12016)Time elapsed: 0.140 s
% 1.41/0.54  % (12016)------------------------------
% 1.41/0.54  % (12016)------------------------------
% 1.41/0.54  % (11987)Success in time 0.175 s
%------------------------------------------------------------------------------

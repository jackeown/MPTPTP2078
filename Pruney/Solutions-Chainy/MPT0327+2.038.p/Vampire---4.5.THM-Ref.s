%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 380 expanded)
%              Number of leaves         :   12 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :   84 ( 633 expanded)
%              Number of equality atoms :   60 ( 299 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f522,plain,(
    $false ),
    inference(subsumption_resolution,[],[f521,f30])).

fof(f30,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f521,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f518,f104])).

fof(f104,plain,(
    sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f102,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f102,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f42,f83])).

fof(f83,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f67,f52])).

fof(f52,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f51,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(sK0),X0) = k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X0)) ),
    inference(superposition,[],[f31,f59])).

fof(f59,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f53,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f53,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f518,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f445,f517])).

fof(f517,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f516,f104])).

fof(f516,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f511,f66])).

fof(f66,plain,(
    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f64,f52])).

fof(f64,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f42,f53])).

fof(f511,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(superposition,[],[f73,f70])).

fof(f70,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f69,f68])).

fof(f68,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f42,f59])).

fof(f69,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(superposition,[],[f38,f59])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X0) ),
    inference(superposition,[],[f47,f68])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f445,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f121,f443])).

fof(f443,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f441,f66])).

fof(f441,plain,(
    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f42,f271])).

fof(f271,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f160,f43])).

fof(f160,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(sK0),X1) = k3_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X1)) ),
    inference(forward_demodulation,[],[f159,f67])).

fof(f159,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(sK0),X1) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X1))) ),
    inference(forward_demodulation,[],[f152,f42])).

fof(f152,plain,(
    ! [X1] : k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X1))) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)) ),
    inference(superposition,[],[f82,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f82,plain,(
    ! [X4] : k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X4)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X4)) ),
    inference(forward_demodulation,[],[f79,f76])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X0)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f63,f36])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK0),X0) ),
    inference(superposition,[],[f31,f53])).

fof(f79,plain,(
    ! [X4] : k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X4)) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X4)) ),
    inference(superposition,[],[f42,f63])).

fof(f121,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f120,f63])).

fof(f120,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f119,f37])).

fof(f119,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) ),
    inference(superposition,[],[f38,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:38:44 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.54  % (6207)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (6208)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.55  % (6218)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.55  % (6209)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.55  % (6227)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.55  % (6229)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.56  % (6216)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.56  % (6228)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.56  % (6217)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.58  % (6218)Refutation not found, incomplete strategy% (6218)------------------------------
% 0.23/0.58  % (6218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (6218)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (6218)Memory used [KB]: 10618
% 0.23/0.58  % (6218)Time elapsed: 0.142 s
% 0.23/0.58  % (6218)------------------------------
% 0.23/0.58  % (6218)------------------------------
% 0.23/0.59  % (6204)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.60  % (6216)Refutation found. Thanks to Tanya!
% 0.23/0.60  % SZS status Theorem for theBenchmark
% 0.23/0.60  % SZS output start Proof for theBenchmark
% 0.23/0.60  fof(f522,plain,(
% 0.23/0.60    $false),
% 0.23/0.60    inference(subsumption_resolution,[],[f521,f30])).
% 0.23/0.60  fof(f30,plain,(
% 0.23/0.60    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.23/0.60    inference(cnf_transformation,[],[f25])).
% 0.23/0.60  fof(f25,plain,(
% 0.23/0.60    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.23/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 0.23/0.60  fof(f24,plain,(
% 0.23/0.60    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.23/0.60    introduced(choice_axiom,[])).
% 0.23/0.60  fof(f21,plain,(
% 0.23/0.60    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.23/0.60    inference(ennf_transformation,[],[f19])).
% 0.23/0.60  fof(f19,negated_conjecture,(
% 0.23/0.60    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.23/0.60    inference(negated_conjecture,[],[f18])).
% 0.23/0.60  fof(f18,conjecture,(
% 0.23/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.23/0.60  fof(f521,plain,(
% 0.23/0.60    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.23/0.60    inference(forward_demodulation,[],[f518,f104])).
% 0.23/0.60  fof(f104,plain,(
% 0.23/0.60    sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 0.23/0.60    inference(forward_demodulation,[],[f102,f43])).
% 0.23/0.60  fof(f43,plain,(
% 0.23/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.60    inference(cnf_transformation,[],[f6])).
% 0.23/0.60  fof(f6,axiom,(
% 0.23/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.60  fof(f102,plain,(
% 0.23/0.60    k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.23/0.60    inference(superposition,[],[f42,f83])).
% 0.23/0.60  fof(f83,plain,(
% 0.23/0.60    k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0)),
% 0.23/0.60    inference(superposition,[],[f67,f52])).
% 0.23/0.60  fof(f52,plain,(
% 0.23/0.60    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.60    inference(resolution,[],[f51,f41])).
% 0.23/0.60  fof(f41,plain,(
% 0.23/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.60    inference(cnf_transformation,[],[f28])).
% 0.23/0.60  fof(f28,plain,(
% 0.23/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.23/0.60    inference(nnf_transformation,[],[f3])).
% 0.23/0.60  fof(f3,axiom,(
% 0.23/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.23/0.60  fof(f51,plain,(
% 0.23/0.60    r1_tarski(k1_tarski(sK0),sK1)),
% 0.23/0.60    inference(resolution,[],[f29,f44])).
% 0.23/0.60  fof(f44,plain,(
% 0.23/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f23])).
% 0.23/0.60  fof(f23,plain,(
% 0.23/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.23/0.60    inference(ennf_transformation,[],[f20])).
% 0.23/0.60  fof(f20,plain,(
% 0.23/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.23/0.60    inference(unused_predicate_definition_removal,[],[f15])).
% 0.23/0.60  fof(f15,axiom,(
% 0.23/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.23/0.60  fof(f29,plain,(
% 0.23/0.60    r2_hidden(sK0,sK1)),
% 0.23/0.60    inference(cnf_transformation,[],[f25])).
% 0.23/0.60  fof(f67,plain,(
% 0.23/0.60    ( ! [X0] : (k4_xboole_0(k1_tarski(sK0),X0) = k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X0))) )),
% 0.23/0.60    inference(superposition,[],[f31,f59])).
% 0.23/0.60  fof(f59,plain,(
% 0.23/0.60    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.23/0.60    inference(superposition,[],[f53,f37])).
% 0.23/0.60  fof(f37,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f1])).
% 0.23/0.60  fof(f1,axiom,(
% 0.23/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.60  fof(f53,plain,(
% 0.23/0.60    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.60    inference(resolution,[],[f51,f35])).
% 0.23/0.60  fof(f35,plain,(
% 0.23/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.60    inference(cnf_transformation,[],[f22])).
% 0.23/0.60  fof(f22,plain,(
% 0.23/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.60    inference(ennf_transformation,[],[f5])).
% 0.23/0.60  fof(f5,axiom,(
% 0.23/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.60  fof(f31,plain,(
% 0.23/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.23/0.60    inference(cnf_transformation,[],[f8])).
% 0.23/0.60  fof(f8,axiom,(
% 0.23/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.23/0.60  fof(f42,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.60    inference(cnf_transformation,[],[f4])).
% 0.23/0.60  fof(f4,axiom,(
% 0.23/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.60  fof(f518,plain,(
% 0.23/0.60    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.23/0.60    inference(backward_demodulation,[],[f445,f517])).
% 0.23/0.60  fof(f517,plain,(
% 0.23/0.60    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.23/0.60    inference(forward_demodulation,[],[f516,f104])).
% 0.23/0.60  fof(f516,plain,(
% 0.23/0.60    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.23/0.60    inference(forward_demodulation,[],[f511,f66])).
% 0.23/0.60  fof(f66,plain,(
% 0.23/0.60    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.23/0.60    inference(forward_demodulation,[],[f64,f52])).
% 0.23/0.60  fof(f64,plain,(
% 0.23/0.60    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.23/0.60    inference(superposition,[],[f42,f53])).
% 0.23/0.60  fof(f511,plain,(
% 0.23/0.60    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 0.23/0.60    inference(superposition,[],[f73,f70])).
% 0.23/0.60  fof(f70,plain,(
% 0.23/0.60    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.23/0.60    inference(forward_demodulation,[],[f69,f68])).
% 0.23/0.60  fof(f68,plain,(
% 0.23/0.60    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 0.23/0.60    inference(superposition,[],[f42,f59])).
% 0.23/0.60  fof(f69,plain,(
% 0.23/0.60    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.23/0.60    inference(superposition,[],[f38,f59])).
% 0.23/0.60  fof(f38,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.23/0.60    inference(cnf_transformation,[],[f10])).
% 0.23/0.60  fof(f10,axiom,(
% 0.23/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.23/0.60  fof(f73,plain,(
% 0.23/0.60    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X0)) )),
% 0.23/0.60    inference(superposition,[],[f47,f68])).
% 0.23/0.60  fof(f47,plain,(
% 0.23/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.23/0.60    inference(cnf_transformation,[],[f9])).
% 0.23/0.60  fof(f9,axiom,(
% 0.23/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.23/0.60  fof(f445,plain,(
% 0.23/0.60    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_xboole_0)),
% 0.23/0.60    inference(backward_demodulation,[],[f121,f443])).
% 0.23/0.60  fof(f443,plain,(
% 0.23/0.60    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.23/0.60    inference(forward_demodulation,[],[f441,f66])).
% 0.23/0.60  fof(f441,plain,(
% 0.23/0.60    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.23/0.60    inference(superposition,[],[f42,f271])).
% 0.23/0.60  fof(f271,plain,(
% 0.23/0.60    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.23/0.60    inference(superposition,[],[f160,f43])).
% 0.23/0.60  fof(f160,plain,(
% 0.23/0.60    ( ! [X1] : (k4_xboole_0(k1_tarski(sK0),X1) = k3_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X1))) )),
% 0.23/0.60    inference(forward_demodulation,[],[f159,f67])).
% 0.23/0.60  fof(f159,plain,(
% 0.23/0.60    ( ! [X1] : (k4_xboole_0(k1_tarski(sK0),X1) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X1)))) )),
% 0.23/0.60    inference(forward_demodulation,[],[f152,f42])).
% 0.23/0.60  fof(f152,plain,(
% 0.23/0.60    ( ! [X1] : (k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X1))) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))) )),
% 0.23/0.60    inference(superposition,[],[f82,f36])).
% 0.23/0.60  fof(f36,plain,(
% 0.23/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.60    inference(cnf_transformation,[],[f7])).
% 0.23/0.60  fof(f7,axiom,(
% 0.23/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.60  fof(f82,plain,(
% 0.23/0.60    ( ! [X4] : (k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X4)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X4))) )),
% 0.23/0.60    inference(forward_demodulation,[],[f79,f76])).
% 0.23/0.60  fof(f76,plain,(
% 0.23/0.60    ( ! [X0] : (k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X0)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,X0))) )),
% 0.23/0.60    inference(superposition,[],[f63,f36])).
% 0.23/0.60  fof(f63,plain,(
% 0.23/0.60    ( ! [X0] : (k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK0),X0)) )),
% 0.23/0.60    inference(superposition,[],[f31,f53])).
% 0.23/0.60  fof(f79,plain,(
% 0.23/0.60    ( ! [X4] : (k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X4)) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X4))) )),
% 0.23/0.60    inference(superposition,[],[f42,f63])).
% 0.23/0.60  fof(f121,plain,(
% 0.23/0.60    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 0.23/0.60    inference(forward_demodulation,[],[f120,f63])).
% 0.23/0.60  fof(f120,plain,(
% 0.23/0.60    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.23/0.60    inference(forward_demodulation,[],[f119,f37])).
% 0.23/0.60  fof(f119,plain,(
% 0.23/0.60    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))),
% 0.23/0.60    inference(superposition,[],[f38,f70])).
% 0.23/0.60  % SZS output end Proof for theBenchmark
% 0.23/0.60  % (6216)------------------------------
% 0.23/0.60  % (6216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.60  % (6216)Termination reason: Refutation
% 0.23/0.60  
% 0.23/0.60  % (6216)Memory used [KB]: 2046
% 0.23/0.60  % (6216)Time elapsed: 0.149 s
% 0.23/0.60  % (6216)------------------------------
% 0.23/0.60  % (6216)------------------------------
% 0.23/0.60  % (6200)Success in time 0.222 s
%------------------------------------------------------------------------------

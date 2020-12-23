%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:54 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 781 expanded)
%              Number of leaves         :   13 ( 208 expanded)
%              Depth                    :   24
%              Number of atoms          :  104 (1367 expanded)
%              Number of equality atoms :   73 ( 601 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f949,plain,(
    $false ),
    inference(subsumption_resolution,[],[f948,f30])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f948,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f940,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f940,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f306,f916])).

fof(f916,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f271,f902])).

fof(f902,plain,(
    k1_tarski(sK0) = k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f178,f895])).

fof(f895,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f583,f65])).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK0),X0) ),
    inference(superposition,[],[f31,f53])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
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
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f583,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(resolution,[],[f565,f35])).

fof(f565,plain,(
    r1_tarski(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(trivial_inequality_removal,[],[f564])).

fof(f564,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f39,f270])).

fof(f270,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f269,f73])).

fof(f73,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f70,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f70,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f41,f59])).

fof(f59,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    r1_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(superposition,[],[f42,f52])).

fof(f52,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f269,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f268,f68])).

fof(f68,plain,(
    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f66,f52])).

fof(f66,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f41,f53])).

fof(f268,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f263,f138])).

fof(f138,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),X1)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f82,f82])).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X0)) ),
    inference(superposition,[],[f47,f68])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f263,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f86,f178])).

fof(f86,plain,(
    ! [X4] : k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X4)) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X4)) ),
    inference(superposition,[],[f41,f65])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f178,plain,(
    k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f173,f139])).

fof(f139,plain,(
    k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f82,f68])).

fof(f173,plain,(
    k5_xboole_0(k1_tarski(sK0),k1_xboole_0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f86,f52])).

fof(f271,plain,(
    k1_xboole_0 = k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(resolution,[],[f266,f40])).

fof(f266,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(superposition,[],[f42,f178])).

fof(f306,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k4_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f303,f123])).

fof(f123,plain,(
    ! [X4] : k4_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X4)) = k5_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X4)) ),
    inference(superposition,[],[f41,f78])).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(sK0),X0) = k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X0)) ),
    inference(superposition,[],[f31,f61])).

fof(f61,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f53,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f303,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f153,f302])).

fof(f302,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f301,f134])).

fof(f134,plain,(
    sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f131,f43])).

fof(f131,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f41,f120])).

fof(f120,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f78,f52])).

fof(f301,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f296,f68])).

fof(f296,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(superposition,[],[f110,f81])).

fof(f81,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f80,f79])).

fof(f79,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f41,f61])).

fof(f80,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(superposition,[],[f37,f61])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X0) ),
    inference(superposition,[],[f47,f79])).

fof(f153,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f152,f65])).

fof(f152,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f151,f36])).

fof(f151,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) ),
    inference(superposition,[],[f37,f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (27722)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (27714)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (27706)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27701)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (27700)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (27711)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (27713)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (27710)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (27727)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (27719)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (27707)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (27702)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (27729)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (27729)Refutation not found, incomplete strategy% (27729)------------------------------
% 0.21/0.52  % (27729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27729)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27729)Memory used [KB]: 1663
% 0.21/0.52  % (27729)Time elapsed: 0.124 s
% 0.21/0.52  % (27729)------------------------------
% 0.21/0.52  % (27729)------------------------------
% 0.21/0.52  % (27709)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (27724)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (27721)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (27712)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (27704)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (27703)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (27705)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (27710)Refutation not found, incomplete strategy% (27710)------------------------------
% 0.21/0.53  % (27710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27710)Memory used [KB]: 10746
% 0.21/0.53  % (27710)Time elapsed: 0.120 s
% 0.21/0.53  % (27710)------------------------------
% 0.21/0.53  % (27710)------------------------------
% 0.21/0.53  % (27723)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (27726)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (27720)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (27715)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (27727)Refutation not found, incomplete strategy% (27727)------------------------------
% 0.21/0.54  % (27727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27727)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27727)Memory used [KB]: 6140
% 0.21/0.54  % (27727)Time elapsed: 0.140 s
% 0.21/0.54  % (27727)------------------------------
% 0.21/0.54  % (27727)------------------------------
% 0.21/0.54  % (27728)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (27716)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (27716)Refutation not found, incomplete strategy% (27716)------------------------------
% 0.21/0.54  % (27716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27716)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27716)Memory used [KB]: 10618
% 0.21/0.54  % (27716)Time elapsed: 0.140 s
% 0.21/0.54  % (27716)------------------------------
% 0.21/0.54  % (27716)------------------------------
% 0.21/0.54  % (27725)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (27718)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (27708)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (27718)Refutation not found, incomplete strategy% (27718)------------------------------
% 0.21/0.54  % (27718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27718)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27718)Memory used [KB]: 1663
% 0.21/0.54  % (27718)Time elapsed: 0.139 s
% 0.21/0.54  % (27718)------------------------------
% 0.21/0.54  % (27718)------------------------------
% 0.21/0.54  % (27717)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (27728)Refutation not found, incomplete strategy% (27728)------------------------------
% 0.21/0.55  % (27728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27728)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27728)Memory used [KB]: 10746
% 0.21/0.55  % (27728)Time elapsed: 0.153 s
% 0.21/0.55  % (27728)------------------------------
% 0.21/0.55  % (27728)------------------------------
% 1.60/0.58  % (27714)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f949,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(subsumption_resolution,[],[f948,f30])).
% 1.60/0.58  fof(f30,plain,(
% 1.60/0.58    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.60/0.58    inference(cnf_transformation,[],[f25])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 1.60/0.58  fof(f24,plain,(
% 1.60/0.58    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f21,plain,(
% 1.60/0.58    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f19])).
% 1.60/0.58  fof(f19,negated_conjecture,(
% 1.60/0.58    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.60/0.58    inference(negated_conjecture,[],[f18])).
% 1.60/0.58  fof(f18,conjecture,(
% 1.60/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.60/0.58  fof(f948,plain,(
% 1.60/0.58    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.60/0.58    inference(forward_demodulation,[],[f940,f43])).
% 1.60/0.58  fof(f43,plain,(
% 1.60/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f7])).
% 1.60/0.58  fof(f7,axiom,(
% 1.60/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.60/0.58  fof(f940,plain,(
% 1.60/0.58    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.60/0.58    inference(backward_demodulation,[],[f306,f916])).
% 1.60/0.58  fof(f916,plain,(
% 1.60/0.58    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.60/0.58    inference(backward_demodulation,[],[f271,f902])).
% 1.60/0.58  fof(f902,plain,(
% 1.60/0.58    k1_tarski(sK0) = k5_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 1.60/0.58    inference(backward_demodulation,[],[f178,f895])).
% 1.60/0.58  fof(f895,plain,(
% 1.60/0.58    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK1))),
% 1.60/0.58    inference(superposition,[],[f583,f65])).
% 1.60/0.58  fof(f65,plain,(
% 1.60/0.58    ( ! [X0] : (k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK0),X0)) )),
% 1.60/0.58    inference(superposition,[],[f31,f53])).
% 1.60/0.58  fof(f53,plain,(
% 1.60/0.58    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.60/0.58    inference(resolution,[],[f51,f35])).
% 1.60/0.58  fof(f35,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f22])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.58  fof(f51,plain,(
% 1.60/0.58    r1_tarski(k1_tarski(sK0),sK1)),
% 1.60/0.58    inference(resolution,[],[f29,f45])).
% 1.60/0.58  fof(f45,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f23])).
% 1.60/0.58  fof(f23,plain,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f20])).
% 1.60/0.58  fof(f20,plain,(
% 1.60/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 1.60/0.58    inference(unused_predicate_definition_removal,[],[f16])).
% 1.60/0.58  fof(f16,axiom,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    r2_hidden(sK0,sK1)),
% 1.60/0.58    inference(cnf_transformation,[],[f25])).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f8])).
% 1.60/0.58  fof(f8,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.60/0.58  fof(f583,plain,(
% 1.60/0.58    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.60/0.58    inference(resolution,[],[f565,f35])).
% 1.60/0.58  fof(f565,plain,(
% 1.60/0.58    r1_tarski(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.60/0.58    inference(trivial_inequality_removal,[],[f564])).
% 1.60/0.58  fof(f564,plain,(
% 1.60/0.58    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.60/0.58    inference(superposition,[],[f39,f270])).
% 1.60/0.58  fof(f270,plain,(
% 1.60/0.58    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.60/0.58    inference(forward_demodulation,[],[f269,f73])).
% 1.60/0.58  fof(f73,plain,(
% 1.60/0.58    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.60/0.58    inference(forward_demodulation,[],[f70,f44])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f9])).
% 1.60/0.58  fof(f9,axiom,(
% 1.60/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.60/0.58  fof(f70,plain,(
% 1.60/0.58    k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f41,f59])).
% 1.60/0.58  fof(f59,plain,(
% 1.60/0.58    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 1.60/0.58    inference(resolution,[],[f55,f35])).
% 1.60/0.58  fof(f55,plain,(
% 1.60/0.58    r1_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.60/0.58    inference(superposition,[],[f42,f52])).
% 1.60/0.58  fof(f52,plain,(
% 1.60/0.58    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.60/0.58    inference(resolution,[],[f51,f40])).
% 1.60/0.58  fof(f40,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.60/0.58    inference(nnf_transformation,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.60/0.58  fof(f42,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f6])).
% 1.60/0.58  fof(f6,axiom,(
% 1.60/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f4])).
% 1.60/0.58  fof(f4,axiom,(
% 1.60/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.58  fof(f269,plain,(
% 1.60/0.58    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.60/0.58    inference(forward_demodulation,[],[f268,f68])).
% 1.60/0.58  fof(f68,plain,(
% 1.60/0.58    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.60/0.58    inference(forward_demodulation,[],[f66,f52])).
% 1.60/0.58  fof(f66,plain,(
% 1.60/0.58    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.60/0.58    inference(superposition,[],[f41,f53])).
% 1.60/0.58  fof(f268,plain,(
% 1.60/0.58    k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.60/0.58    inference(forward_demodulation,[],[f263,f138])).
% 1.60/0.58  fof(f138,plain,(
% 1.60/0.58    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_tarski(sK0),X1)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,X1))) )),
% 1.60/0.58    inference(superposition,[],[f82,f82])).
% 1.60/0.58  fof(f82,plain,(
% 1.60/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X0))) )),
% 1.60/0.58    inference(superposition,[],[f47,f68])).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f10])).
% 1.60/0.58  fof(f10,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.60/0.58  fof(f263,plain,(
% 1.60/0.58    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_xboole_0,k1_tarski(sK0))) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 1.60/0.58    inference(superposition,[],[f86,f178])).
% 1.60/0.58  fof(f86,plain,(
% 1.60/0.58    ( ! [X4] : (k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,X4)) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X4))) )),
% 1.60/0.58    inference(superposition,[],[f41,f65])).
% 1.60/0.58  fof(f39,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f178,plain,(
% 1.60/0.58    k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK1))),
% 1.60/0.58    inference(forward_demodulation,[],[f173,f139])).
% 1.60/0.58  fof(f139,plain,(
% 1.60/0.58    k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f82,f68])).
% 1.60/0.58  fof(f173,plain,(
% 1.60/0.58    k5_xboole_0(k1_tarski(sK0),k1_xboole_0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,sK1))),
% 1.60/0.58    inference(superposition,[],[f86,f52])).
% 1.60/0.58  fof(f271,plain,(
% 1.60/0.58    k1_xboole_0 = k4_xboole_0(k5_xboole_0(k1_xboole_0,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.60/0.58    inference(resolution,[],[f266,f40])).
% 1.60/0.58  fof(f266,plain,(
% 1.60/0.58    r1_tarski(k5_xboole_0(k1_xboole_0,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.60/0.58    inference(superposition,[],[f42,f178])).
% 1.60/0.58  fof(f306,plain,(
% 1.60/0.58    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k4_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 1.60/0.58    inference(forward_demodulation,[],[f303,f123])).
% 1.60/0.58  fof(f123,plain,(
% 1.60/0.58    ( ! [X4] : (k4_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X4)) = k5_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X4))) )),
% 1.60/0.58    inference(superposition,[],[f41,f78])).
% 1.60/0.58  fof(f78,plain,(
% 1.60/0.58    ( ! [X0] : (k4_xboole_0(k1_tarski(sK0),X0) = k3_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),X0))) )),
% 1.60/0.58    inference(superposition,[],[f31,f61])).
% 1.60/0.58  fof(f61,plain,(
% 1.60/0.58    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.60/0.58    inference(superposition,[],[f53,f36])).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f1])).
% 1.60/0.58  fof(f1,axiom,(
% 1.60/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.58  fof(f303,plain,(
% 1.60/0.58    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 1.60/0.58    inference(backward_demodulation,[],[f153,f302])).
% 1.60/0.58  fof(f302,plain,(
% 1.60/0.58    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.60/0.58    inference(forward_demodulation,[],[f301,f134])).
% 1.60/0.58  fof(f134,plain,(
% 1.60/0.58    sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 1.60/0.58    inference(forward_demodulation,[],[f131,f43])).
% 1.60/0.58  fof(f131,plain,(
% 1.60/0.58    k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f41,f120])).
% 1.60/0.58  fof(f120,plain,(
% 1.60/0.58    k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f78,f52])).
% 1.60/0.58  fof(f301,plain,(
% 1.60/0.58    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.60/0.58    inference(forward_demodulation,[],[f296,f68])).
% 1.60/0.58  fof(f296,plain,(
% 1.60/0.58    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 1.60/0.58    inference(superposition,[],[f110,f81])).
% 1.60/0.58  fof(f81,plain,(
% 1.60/0.58    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.60/0.58    inference(forward_demodulation,[],[f80,f79])).
% 1.60/0.58  fof(f79,plain,(
% 1.60/0.58    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 1.60/0.58    inference(superposition,[],[f41,f61])).
% 1.60/0.58  fof(f80,plain,(
% 1.60/0.58    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.60/0.58    inference(superposition,[],[f37,f61])).
% 1.60/0.58  fof(f37,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f11])).
% 1.60/0.58  fof(f11,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.60/0.58  fof(f110,plain,(
% 1.60/0.58    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X0)) )),
% 1.60/0.58    inference(superposition,[],[f47,f79])).
% 1.60/0.58  fof(f153,plain,(
% 1.60/0.58    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 1.60/0.58    inference(forward_demodulation,[],[f152,f65])).
% 1.60/0.58  fof(f152,plain,(
% 1.60/0.58    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 1.60/0.58    inference(forward_demodulation,[],[f151,f36])).
% 1.60/0.58  fof(f151,plain,(
% 1.60/0.58    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))),
% 1.60/0.58    inference(superposition,[],[f37,f81])).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (27714)------------------------------
% 1.60/0.58  % (27714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (27714)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (27714)Memory used [KB]: 2558
% 1.60/0.58  % (27714)Time elapsed: 0.125 s
% 1.60/0.58  % (27714)------------------------------
% 1.60/0.58  % (27714)------------------------------
% 1.60/0.58  % (27699)Success in time 0.224 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  19 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(subsumption_resolution,[],[f30,f7])).

fof(f7,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
       => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f30,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f16,f11])).

fof(f11,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f8,f6])).

fof(f6,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f9,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:43:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (5744)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (5748)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (5744)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f30,f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ~r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X1),X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.42    inference(negated_conjecture,[],[f3])).
% 0.20/0.42  fof(f3,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.42    inference(superposition,[],[f16,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(resolution,[],[f8,f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.20/0.42    inference(superposition,[],[f9,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (5744)------------------------------
% 0.20/0.42  % (5744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (5744)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (5744)Memory used [KB]: 10618
% 0.20/0.42  % (5744)Time elapsed: 0.005 s
% 0.20/0.42  % (5744)------------------------------
% 0.20/0.42  % (5744)------------------------------
% 0.20/0.42  % (5742)Success in time 0.062 s
%------------------------------------------------------------------------------

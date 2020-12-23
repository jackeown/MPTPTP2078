%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(subsumption_resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f24,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f71,plain,(
    k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f63,f48])).

fof(f48,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f19,f45])).

fof(f45,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f16,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f63,plain,(
    k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f28,f24])).

fof(f28,plain,(
    k4_xboole_0(sK2,sK1) != k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f25,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:29:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.44  % (7558)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (7553)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (7555)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.45  % (7555)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f71,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 0.21/0.45    inference(superposition,[],[f24,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,k2_xboole_0(sK1,k1_xboole_0))),
% 0.21/0.45    inference(forward_demodulation,[],[f63,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.45    inference(superposition,[],[f19,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f16,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,k2_xboole_0(sK1,sK0))),
% 0.21/0.45    inference(superposition,[],[f28,f24])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    k4_xboole_0(sK2,sK1) != k4_xboole_0(k4_xboole_0(sK2,sK1),sK0)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f25,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ~r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f17,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (7555)------------------------------
% 0.21/0.45  % (7555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (7555)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (7555)Memory used [KB]: 6140
% 0.21/0.45  % (7555)Time elapsed: 0.005 s
% 0.21/0.45  % (7555)------------------------------
% 0.21/0.45  % (7555)------------------------------
% 0.21/0.45  % (7549)Success in time 0.081 s
%------------------------------------------------------------------------------

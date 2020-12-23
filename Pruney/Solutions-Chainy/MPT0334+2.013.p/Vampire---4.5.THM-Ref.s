%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:13 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   22 (  41 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  57 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(subsumption_resolution,[],[f30,f11])).

% (2753)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f11,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f30,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),k2_enumset1(sK1,sK1,sK1,sK1)) != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f18,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k2_enumset1(X2,X2,X2,X2),X0)),k2_enumset1(X1,X1,X1,X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f16,f13,f13])).

fof(f13,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X1,X2)),X0) ) ),
    inference(definition_unfolding,[],[f17,f15,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f18,plain,(
    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),k2_enumset1(sK1,sK1,sK1,sK1)) != k5_xboole_0(k4_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f12,f15,f13,f13,f15,f13,f13])).

fof(f12,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n007.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:32:21 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.43  % (2755)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.46  % (2755)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f31,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(subsumption_resolution,[],[f30,f11])).
% 0.18/0.46  % (2753)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  fof(f11,plain,(
% 0.18/0.46    sK0 != sK1),
% 0.18/0.46    inference(cnf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,plain,(
% 0.18/0.46    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 0.18/0.46    inference(ennf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,negated_conjecture,(
% 0.18/0.46    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.18/0.46    inference(negated_conjecture,[],[f6])).
% 0.18/0.46  fof(f6,conjecture,(
% 0.18/0.46    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    sK0 = sK1),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f27])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),k2_enumset1(sK1,sK1,sK1,sK1)) != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 0.18/0.46    inference(superposition,[],[f18,f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k2_enumset1(X2,X2,X2,X2),X0)),k2_enumset1(X1,X1,X1,X1)) | X1 = X2) )),
% 0.18/0.46    inference(resolution,[],[f21,f20])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.18/0.46    inference(definition_unfolding,[],[f16,f13,f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f9])).
% 0.18/0.46  fof(f9,plain,(
% 0.18/0.46    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.18/0.46    inference(ennf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X1,X2)),X0)) )),
% 0.18/0.46    inference(definition_unfolding,[],[f17,f15,f15])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f10])).
% 0.18/0.46  fof(f10,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),k2_enumset1(sK1,sK1,sK1,sK1)) != k5_xboole_0(k4_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 0.18/0.46    inference(definition_unfolding,[],[f12,f15,f13,f13,f15,f13,f13])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 0.18/0.46    inference(cnf_transformation,[],[f8])).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (2755)------------------------------
% 0.18/0.46  % (2755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (2755)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (2755)Memory used [KB]: 6268
% 0.18/0.46  % (2755)Time elapsed: 0.086 s
% 0.18/0.46  % (2755)------------------------------
% 0.18/0.46  % (2755)------------------------------
% 0.18/0.47  % (2746)Success in time 0.13 s
%------------------------------------------------------------------------------

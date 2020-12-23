%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  65 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :   51 ( 116 expanded)
%              Number of equality atoms :   31 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) ),
    inference(forward_demodulation,[],[f58,f28])).

fof(f28,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f23,f26])).

fof(f26,plain,(
    sK3 = k2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f19,f14])).

fof(f14,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f58,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f51,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f18,f18])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
    inference(superposition,[],[f21,f37])).

fof(f37,plain,(
    ! [X12,X13] : k4_xboole_0(k2_zfmisc_1(sK0,X12),k4_xboole_0(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK1,X13))) = k2_zfmisc_1(sK0,k4_xboole_0(X12,k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f23,f25])).

fof(f25,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f19,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f20,f18,f18,f18])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f21,plain,(
    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f15,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:13:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.41  % (11337)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.41  % (11337)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(trivial_inequality_removal,[],[f59])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)),
% 0.21/0.41    inference(forward_demodulation,[],[f58,f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),
% 0.21/0.41    inference(superposition,[],[f23,f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    sK3 = k2_xboole_0(sK2,sK3)),
% 0.21/0.41    inference(resolution,[],[f19,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    r1_tarski(sK2,sK3)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.41    inference(flattening,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.21/0.41    inference(negated_conjecture,[],[f6])).
% 0.21/0.41  fof(f6,conjecture,(
% 0.21/0.41    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.21/0.41    inference(definition_unfolding,[],[f17,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 0.21/0.41    inference(forward_demodulation,[],[f51,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.41    inference(definition_unfolding,[],[f16,f18,f18])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))),
% 0.21/0.41    inference(superposition,[],[f21,f37])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    ( ! [X12,X13] : (k4_xboole_0(k2_zfmisc_1(sK0,X12),k4_xboole_0(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK1,X13))) = k2_zfmisc_1(sK0,k4_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 0.21/0.41    inference(superposition,[],[f24,f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.41    inference(superposition,[],[f23,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.41    inference(resolution,[],[f19,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    r1_tarski(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.21/0.41    inference(definition_unfolding,[],[f20,f18,f18,f18])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.41    inference(definition_unfolding,[],[f15,f18])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (11337)------------------------------
% 0.21/0.41  % (11337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (11337)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (11337)Memory used [KB]: 1663
% 0.21/0.41  % (11337)Time elapsed: 0.005 s
% 0.21/0.41  % (11337)------------------------------
% 0.21/0.41  % (11337)------------------------------
% 0.21/0.41  % (11324)Success in time 0.059 s
%------------------------------------------------------------------------------

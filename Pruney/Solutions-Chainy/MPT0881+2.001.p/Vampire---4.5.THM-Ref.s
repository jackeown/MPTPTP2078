%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  34 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  37 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f30,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2))) ),
    inference(definition_unfolding,[],[f22,f17,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f30,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(k4_tarski(sK0,sK2))),k1_tarski(sK3)) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2))) ),
    inference(definition_unfolding,[],[f23,f17,f17])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3)),k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3))) ),
    inference(definition_unfolding,[],[f15,f20,f17,f17,f21,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f15,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (30088)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (30088)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f30,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f22,f17,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(k4_tarski(sK0,sK2))),k1_tarski(sK3))),
% 0.20/0.48    inference(superposition,[],[f24,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f23,f17,f17])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3)),k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3)))),
% 0.20/0.48    inference(definition_unfolding,[],[f15,f20,f17,f17,f21,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_mcart_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (30088)------------------------------
% 0.20/0.48  % (30088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30088)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (30088)Memory used [KB]: 6140
% 0.20/0.48  % (30088)Time elapsed: 0.074 s
% 0.20/0.48  % (30088)------------------------------
% 0.20/0.48  % (30088)------------------------------
% 0.20/0.48  % (30075)Success in time 0.122 s
%------------------------------------------------------------------------------

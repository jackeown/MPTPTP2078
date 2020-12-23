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
% DateTime   : Thu Dec  3 12:58:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  30 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  33 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f20])).

fof(f20,plain,(
    k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)) ),
    inference(superposition,[],[f19,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2)) ),
    inference(definition_unfolding,[],[f15,f11])).

fof(f11,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f19,plain,(
    k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK3)) ),
    inference(backward_demodulation,[],[f16,f17])).

fof(f16,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f10,f12,f11,f11,f13,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f10,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (14065)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.44  % (14065)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3))),
% 0.21/0.44    inference(superposition,[],[f19,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f15,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK3))),
% 0.21/0.44    inference(backward_demodulation,[],[f16,f17])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)),k2_tarski(sK3,sK3)) != k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3))),
% 0.21/0.44    inference(definition_unfolding,[],[f10,f12,f11,f11,f13,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (14065)------------------------------
% 0.21/0.44  % (14065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (14065)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (14065)Memory used [KB]: 1535
% 0.21/0.44  % (14065)Time elapsed: 0.005 s
% 0.21/0.44  % (14065)------------------------------
% 0.21/0.44  % (14065)------------------------------
% 0.21/0.45  % (14059)Success in time 0.085 s
%------------------------------------------------------------------------------

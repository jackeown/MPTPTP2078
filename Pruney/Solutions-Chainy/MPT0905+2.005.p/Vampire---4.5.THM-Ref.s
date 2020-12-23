%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   16 (  20 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   17 (  21 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f22,plain,(
    k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f21,f13])).

fof(f21,plain,(
    k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2)),k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f19,f13])).

fof(f19,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f12,f18,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f12,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))
   => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:51:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.42  % (13462)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.42  % (13462)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(subsumption_resolution,[],[f22,f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k1_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2)),k1_tarski(sK3))),
% 0.19/0.42    inference(forward_demodulation,[],[f21,f13])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(k4_tarski(sK0,sK1)),k1_tarski(sK2)),k1_tarski(sK3))),
% 0.19/0.42    inference(backward_demodulation,[],[f19,f13])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) != k1_tarski(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))),
% 0.19/0.42    inference(definition_unfolding,[],[f12,f18,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3)) => k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) != k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.19/0.42    inference(ennf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.19/0.42    inference(negated_conjecture,[],[f7])).
% 0.19/0.42  fof(f7,conjecture,(
% 0.19/0.42    ! [X0,X1,X2,X3] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) = k1_tarski(k4_mcart_1(X0,X1,X2,X3))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_mcart_1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (13462)------------------------------
% 0.19/0.42  % (13462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (13462)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (13462)Memory used [KB]: 1535
% 0.19/0.42  % (13462)Time elapsed: 0.003 s
% 0.19/0.42  % (13462)------------------------------
% 0.19/0.42  % (13462)------------------------------
% 0.19/0.42  % (13448)Success in time 0.073 s
%------------------------------------------------------------------------------

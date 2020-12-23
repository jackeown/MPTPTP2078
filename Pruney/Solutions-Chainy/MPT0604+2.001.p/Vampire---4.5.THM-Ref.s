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
% DateTime   : Thu Dec  3 12:51:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11,f9])).

fof(f9,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f11,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(superposition,[],[f8,f10])).

fof(f10,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

fof(f8,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0)))
   => k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t208_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (21548)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (21548)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f11,f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.21/0.46    inference(superposition,[],[f8,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0))) => k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t208_relat_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21548)------------------------------
% 0.21/0.46  % (21548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21548)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21548)Memory used [KB]: 1535
% 0.21/0.46  % (21548)Time elapsed: 0.005 s
% 0.21/0.46  % (21548)------------------------------
% 0.21/0.46  % (21548)------------------------------
% 0.21/0.46  % (21544)Success in time 0.103 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  23 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  24 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f11,f13])).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5)) ),
    inference(definition_unfolding,[],[f12,f10])).

fof(f10,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f12,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f15,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f9,f10,f13])).

fof(f9,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:30:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.39  % (2679)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.39  % (2679)Refutation found. Thanks to Tanya!
% 0.20/0.39  % SZS status Theorem for theBenchmark
% 0.20/0.39  % SZS output start Proof for theBenchmark
% 0.20/0.39  fof(f16,plain,(
% 0.20/0.39    $false),
% 0.20/0.39    inference(subsumption_resolution,[],[f15,f14])).
% 0.20/0.39  fof(f14,plain,(
% 0.20/0.39    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) )),
% 0.20/0.39    inference(definition_unfolding,[],[f11,f13])).
% 0.20/0.39  fof(f13,plain,(
% 0.20/0.39    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5))) )),
% 0.20/0.39    inference(definition_unfolding,[],[f12,f10])).
% 0.20/0.39  fof(f10,plain,(
% 0.20/0.39    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.20/0.39    inference(cnf_transformation,[],[f3])).
% 0.20/0.39  fof(f3,axiom,(
% 0.20/0.39    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.20/0.39  fof(f12,plain,(
% 0.20/0.39    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.20/0.39    inference(cnf_transformation,[],[f1])).
% 0.20/0.39  fof(f1,axiom,(
% 0.20/0.39    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.20/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.20/0.39  fof(f11,plain,(
% 0.20/0.39    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.39    inference(cnf_transformation,[],[f2])).
% 0.20/0.39  fof(f2,axiom,(
% 0.20/0.39    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 0.20/0.39  fof(f15,plain,(
% 0.20/0.39    k2_enumset1(sK0,sK0,sK0,sK0) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.39    inference(definition_unfolding,[],[f9,f10,f13])).
% 0.20/0.39  fof(f9,plain,(
% 0.20/0.39    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.39    inference(cnf_transformation,[],[f8])).
% 0.20/0.39  fof(f8,plain,(
% 0.20/0.39    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.20/0.39  fof(f7,plain,(
% 0.20/0.39    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.39    introduced(choice_axiom,[])).
% 0.20/0.39  fof(f6,plain,(
% 0.20/0.39    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.20/0.39    inference(ennf_transformation,[],[f5])).
% 0.20/0.39  fof(f5,negated_conjecture,(
% 0.20/0.39    ~! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.20/0.39    inference(negated_conjecture,[],[f4])).
% 0.20/0.39  fof(f4,conjecture,(
% 0.20/0.39    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.20/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).
% 0.20/0.39  % SZS output end Proof for theBenchmark
% 0.20/0.39  % (2679)------------------------------
% 0.20/0.39  % (2679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.39  % (2679)Termination reason: Refutation
% 0.20/0.39  
% 0.20/0.39  % (2679)Memory used [KB]: 6012
% 0.20/0.39  % (2679)Time elapsed: 0.002 s
% 0.20/0.39  % (2679)------------------------------
% 0.20/0.39  % (2679)------------------------------
% 0.20/0.40  % (2671)Success in time 0.041 s
%------------------------------------------------------------------------------

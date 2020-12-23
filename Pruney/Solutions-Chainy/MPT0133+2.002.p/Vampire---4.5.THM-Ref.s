%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    6
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f9])).

fof(f9,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(definition_unfolding,[],[f7,f8])).

fof(f8,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f7,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (5726)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.42  % (5726)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4))),
% 0.20/0.42    inference(definition_unfolding,[],[f7,f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4))),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f4,f5])).
% 0.20/0.42  fof(f5,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_tarski(sK3,sK4))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f4,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.42    inference(negated_conjecture,[],[f2])).
% 0.20/0.42  fof(f2,conjecture,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (5726)------------------------------
% 0.20/0.42  % (5726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (5726)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (5726)Memory used [KB]: 6012
% 0.20/0.42  % (5726)Time elapsed: 0.003 s
% 0.20/0.42  % (5726)------------------------------
% 0.20/0.42  % (5726)------------------------------
% 0.20/0.43  % (5711)Success in time 0.067 s
%------------------------------------------------------------------------------

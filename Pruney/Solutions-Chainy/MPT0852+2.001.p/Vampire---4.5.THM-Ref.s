%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  37 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  71 expanded)
%              Number of equality atoms :   24 (  70 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(global_subsumption,[],[f8,f15])).

fof(f15,plain,(
    sK0 != k4_tarski(sK1,sK2) ),
    inference(superposition,[],[f13,f14])).

fof(f14,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f11,f8])).

fof(f11,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f13,plain,(
    sK0 != k4_tarski(sK1,k2_mcart_1(sK0)) ),
    inference(superposition,[],[f9,f12])).

fof(f12,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f10,f8])).

fof(f10,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f9,plain,(
    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f6,f5])).

fof(f5,plain,
    ( ? [X0] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

fof(f8,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (25361)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (25361)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(global_subsumption,[],[f8,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    sK0 != k4_tarski(sK1,sK2)),
% 0.21/0.42    inference(superposition,[],[f13,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k2_mcart_1(sK0) = sK2),
% 0.21/0.42    inference(superposition,[],[f11,f8])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    sK0 != k4_tarski(sK1,k2_mcart_1(sK0))),
% 0.21/0.42    inference(superposition,[],[f9,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    k1_mcart_1(sK0) = sK1),
% 0.21/0.42    inference(superposition,[],[f10,f8])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f6,f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0 & ? [X1,X2] : k4_tarski(X1,X2) = X0) => (sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f4,plain,(
% 0.21/0.42    ? [X0] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0 & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f2])).
% 0.21/0.42  fof(f2,conjecture,(
% 0.21/0.42    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (25361)------------------------------
% 0.21/0.42  % (25361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (25361)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (25361)Memory used [KB]: 6012
% 0.21/0.42  % (25361)Time elapsed: 0.004 s
% 0.21/0.42  % (25361)------------------------------
% 0.21/0.42  % (25361)------------------------------
% 0.21/0.42  % (25356)Success in time 0.06 s
%------------------------------------------------------------------------------

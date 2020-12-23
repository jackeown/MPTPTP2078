%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:55 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  37 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f24])).

fof(f24,plain,(
    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5)) ),
    inference(definition_unfolding,[],[f16,f12])).

fof(f12,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f22,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f14,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

fof(f20,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f11,f17,f18])).

fof(f11,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:36:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (825720832)
% 0.14/0.37  ipcrm: permission denied for id (827097090)
% 0.14/0.37  ipcrm: permission denied for id (827162628)
% 0.14/0.37  ipcrm: permission denied for id (827195397)
% 0.14/0.37  ipcrm: permission denied for id (827228166)
% 0.14/0.37  ipcrm: permission denied for id (827293704)
% 0.14/0.38  ipcrm: permission denied for id (827326473)
% 0.14/0.38  ipcrm: permission denied for id (827392010)
% 0.14/0.38  ipcrm: permission denied for id (825786379)
% 0.14/0.38  ipcrm: permission denied for id (825819148)
% 0.14/0.38  ipcrm: permission denied for id (825851918)
% 0.14/0.38  ipcrm: permission denied for id (827490320)
% 0.14/0.39  ipcrm: permission denied for id (827523089)
% 0.14/0.39  ipcrm: permission denied for id (827555858)
% 0.22/0.39  ipcrm: permission denied for id (827654165)
% 0.22/0.39  ipcrm: permission denied for id (825917462)
% 0.22/0.40  ipcrm: permission denied for id (827752473)
% 0.22/0.40  ipcrm: permission denied for id (827850780)
% 0.22/0.40  ipcrm: permission denied for id (827883549)
% 0.22/0.40  ipcrm: permission denied for id (825983006)
% 0.22/0.40  ipcrm: permission denied for id (826015776)
% 0.22/0.41  ipcrm: permission denied for id (827949089)
% 0.22/0.41  ipcrm: permission denied for id (827981858)
% 0.22/0.41  ipcrm: permission denied for id (826048548)
% 0.22/0.41  ipcrm: permission denied for id (826114086)
% 0.22/0.41  ipcrm: permission denied for id (826146855)
% 0.22/0.41  ipcrm: permission denied for id (828080168)
% 0.22/0.42  ipcrm: permission denied for id (826179626)
% 0.22/0.42  ipcrm: permission denied for id (826212396)
% 0.22/0.42  ipcrm: permission denied for id (828244015)
% 0.22/0.43  ipcrm: permission denied for id (828309553)
% 0.22/0.43  ipcrm: permission denied for id (826245170)
% 0.22/0.43  ipcrm: permission denied for id (826277942)
% 0.22/0.43  ipcrm: permission denied for id (828473400)
% 0.22/0.44  ipcrm: permission denied for id (828506169)
% 0.22/0.44  ipcrm: permission denied for id (826343482)
% 0.22/0.44  ipcrm: permission denied for id (828604477)
% 0.22/0.44  ipcrm: permission denied for id (826409022)
% 0.22/0.44  ipcrm: permission denied for id (826441792)
% 0.22/0.45  ipcrm: permission denied for id (828670017)
% 0.22/0.45  ipcrm: permission denied for id (828702786)
% 0.22/0.45  ipcrm: permission denied for id (828735555)
% 0.22/0.45  ipcrm: permission denied for id (826474564)
% 0.22/0.45  ipcrm: permission denied for id (828768325)
% 0.22/0.45  ipcrm: permission denied for id (826507336)
% 0.22/0.46  ipcrm: permission denied for id (828899402)
% 0.22/0.46  ipcrm: permission denied for id (828964940)
% 0.22/0.46  ipcrm: permission denied for id (826572877)
% 0.22/0.46  ipcrm: permission denied for id (829096017)
% 0.22/0.47  ipcrm: permission denied for id (829128786)
% 0.22/0.47  ipcrm: permission denied for id (829161555)
% 0.22/0.47  ipcrm: permission denied for id (829259862)
% 0.22/0.47  ipcrm: permission denied for id (829292631)
% 0.22/0.47  ipcrm: permission denied for id (829325400)
% 0.22/0.48  ipcrm: permission denied for id (829358169)
% 0.22/0.48  ipcrm: permission denied for id (829554781)
% 0.22/0.48  ipcrm: permission denied for id (829522014)
% 0.22/0.48  ipcrm: permission denied for id (829620320)
% 0.22/0.49  ipcrm: permission denied for id (826671201)
% 0.22/0.49  ipcrm: permission denied for id (829653090)
% 0.22/0.49  ipcrm: permission denied for id (826736741)
% 0.22/0.49  ipcrm: permission denied for id (829816936)
% 0.22/0.50  ipcrm: permission denied for id (829849705)
% 0.22/0.50  ipcrm: permission denied for id (826835050)
% 0.22/0.50  ipcrm: permission denied for id (829915244)
% 0.22/0.50  ipcrm: permission denied for id (829980782)
% 0.22/0.51  ipcrm: permission denied for id (826900594)
% 0.22/0.51  ipcrm: permission denied for id (830144628)
% 0.22/0.51  ipcrm: permission denied for id (830177397)
% 0.22/0.51  ipcrm: permission denied for id (830242935)
% 0.22/0.51  ipcrm: permission denied for id (830275704)
% 0.22/0.51  ipcrm: permission denied for id (830308473)
% 0.22/0.52  ipcrm: permission denied for id (830374011)
% 0.22/0.52  ipcrm: permission denied for id (826998909)
% 0.22/0.52  ipcrm: permission denied for id (830439550)
% 0.22/0.52  ipcrm: permission denied for id (830472319)
% 0.39/0.62  % (20626)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.39/0.62  % (20626)Refutation found. Thanks to Tanya!
% 0.39/0.62  % SZS status Theorem for theBenchmark
% 0.39/0.62  % SZS output start Proof for theBenchmark
% 0.39/0.62  fof(f25,plain,(
% 0.39/0.62    $false),
% 0.39/0.62    inference(trivial_inequality_removal,[],[f24])).
% 0.39/0.62  fof(f24,plain,(
% 0.39/0.62    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.39/0.62    inference(superposition,[],[f22,f19])).
% 0.39/0.62  fof(f19,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) )),
% 0.39/0.62    inference(definition_unfolding,[],[f15,f18])).
% 0.39/0.62  fof(f18,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5))) )),
% 0.39/0.62    inference(definition_unfolding,[],[f16,f12])).
% 0.39/0.62  fof(f12,plain,(
% 0.39/0.62    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f5])).
% 0.39/0.62  fof(f5,axiom,(
% 0.39/0.62    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.39/0.62  fof(f16,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.39/0.62    inference(cnf_transformation,[],[f2])).
% 0.39/0.62  fof(f2,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.39/0.62  fof(f15,plain,(
% 0.39/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f3])).
% 0.39/0.62  fof(f3,axiom,(
% 0.39/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.39/0.62  fof(f22,plain,(
% 0.39/0.62    k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.39/0.62    inference(backward_demodulation,[],[f20,f21])).
% 0.39/0.62  fof(f21,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X2,X2,X2))) )),
% 0.39/0.62    inference(definition_unfolding,[],[f14,f17])).
% 0.39/0.62  fof(f17,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X2,X2,X2))) )),
% 0.39/0.62    inference(definition_unfolding,[],[f13,f12])).
% 0.39/0.62  fof(f13,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.39/0.62    inference(cnf_transformation,[],[f1])).
% 0.39/0.62  fof(f1,axiom,(
% 0.39/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.39/0.62  fof(f14,plain,(
% 0.39/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.39/0.62    inference(cnf_transformation,[],[f4])).
% 0.39/0.62  fof(f4,axiom,(
% 0.39/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).
% 0.39/0.62  fof(f20,plain,(
% 0.39/0.62    k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.39/0.62    inference(definition_unfolding,[],[f11,f17,f18])).
% 0.39/0.62  fof(f11,plain,(
% 0.39/0.62    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.39/0.62    inference(cnf_transformation,[],[f10])).
% 0.39/0.62  fof(f10,plain,(
% 0.39/0.62    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.39/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.39/0.62  fof(f9,plain,(
% 0.39/0.62    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.39/0.62    introduced(choice_axiom,[])).
% 0.39/0.62  fof(f8,plain,(
% 0.39/0.62    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.39/0.62    inference(ennf_transformation,[],[f7])).
% 0.39/0.62  fof(f7,negated_conjecture,(
% 0.39/0.62    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.39/0.62    inference(negated_conjecture,[],[f6])).
% 0.39/0.62  fof(f6,conjecture,(
% 0.39/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.39/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).
% 0.39/0.62  % SZS output end Proof for theBenchmark
% 0.39/0.62  % (20626)------------------------------
% 0.39/0.62  % (20626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.62  % (20626)Termination reason: Refutation
% 0.39/0.62  
% 0.39/0.62  % (20626)Memory used [KB]: 1663
% 0.39/0.62  % (20626)Time elapsed: 0.055 s
% 0.39/0.62  % (20626)------------------------------
% 0.39/0.62  % (20626)------------------------------
% 0.39/0.62  % (20452)Success in time 0.26 s
%------------------------------------------------------------------------------

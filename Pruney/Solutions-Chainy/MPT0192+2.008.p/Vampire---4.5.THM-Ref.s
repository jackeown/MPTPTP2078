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
% DateTime   : Thu Dec  3 12:34:24 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 107 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 ( 108 expanded)
%              Number of equality atoms :   30 ( 107 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f14,f23,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f52,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
    inference(superposition,[],[f35,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3) ),
    inference(definition_unfolding,[],[f16,f23,f23])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_enumset1)).

fof(f35,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK3,sK2) ),
    inference(superposition,[],[f24,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f15,f23,f23])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f24,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK0) ),
    inference(definition_unfolding,[],[f13,f23,f23])).

fof(f13,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (801505280)
% 0.14/0.37  ipcrm: permission denied for id (801538049)
% 0.14/0.37  ipcrm: permission denied for id (801603590)
% 0.14/0.38  ipcrm: permission denied for id (801734668)
% 0.14/0.38  ipcrm: permission denied for id (801767437)
% 0.14/0.38  ipcrm: permission denied for id (801832974)
% 0.14/0.38  ipcrm: permission denied for id (801865743)
% 0.14/0.39  ipcrm: permission denied for id (801898512)
% 0.14/0.39  ipcrm: permission denied for id (801931282)
% 0.14/0.40  ipcrm: permission denied for id (802062360)
% 0.14/0.40  ipcrm: permission denied for id (802095129)
% 0.21/0.41  ipcrm: permission denied for id (802291744)
% 0.21/0.41  ipcrm: permission denied for id (802324515)
% 0.21/0.41  ipcrm: permission denied for id (802357284)
% 0.21/0.41  ipcrm: permission denied for id (802390053)
% 0.21/0.41  ipcrm: permission denied for id (802422823)
% 0.21/0.42  ipcrm: permission denied for id (802455593)
% 0.21/0.43  ipcrm: permission denied for id (802619444)
% 0.21/0.43  ipcrm: permission denied for id (802684982)
% 0.21/0.44  ipcrm: permission denied for id (802717752)
% 0.21/0.44  ipcrm: permission denied for id (802750521)
% 0.21/0.44  ipcrm: permission denied for id (802783290)
% 0.21/0.45  ipcrm: permission denied for id (802947136)
% 0.21/0.46  ipcrm: permission denied for id (803110984)
% 0.21/0.46  ipcrm: permission denied for id (803176523)
% 0.21/0.46  ipcrm: permission denied for id (803242064)
% 0.21/0.47  ipcrm: permission denied for id (803307602)
% 0.21/0.47  ipcrm: permission denied for id (803340371)
% 0.21/0.47  ipcrm: permission denied for id (803405910)
% 0.21/0.48  ipcrm: permission denied for id (803536987)
% 0.21/0.49  ipcrm: permission denied for id (803602528)
% 0.21/0.49  ipcrm: permission denied for id (803635300)
% 0.21/0.49  ipcrm: permission denied for id (803700839)
% 0.21/0.50  ipcrm: permission denied for id (803733609)
% 0.21/0.50  ipcrm: permission denied for id (803864685)
% 0.21/0.50  ipcrm: permission denied for id (803897455)
% 0.21/0.51  ipcrm: permission denied for id (803962993)
% 0.21/0.51  ipcrm: permission denied for id (804028531)
% 0.21/0.51  ipcrm: permission denied for id (804159608)
% 0.21/0.52  ipcrm: permission denied for id (804323454)
% 0.76/0.60  % (19014)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.76/0.60  % (19014)Refutation found. Thanks to Tanya!
% 0.76/0.60  % SZS status Theorem for theBenchmark
% 0.76/0.60  % SZS output start Proof for theBenchmark
% 0.76/0.60  fof(f61,plain,(
% 0.76/0.60    $false),
% 0.76/0.60    inference(subsumption_resolution,[],[f52,f25])).
% 0.76/0.60  fof(f25,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1)) )),
% 0.76/0.60    inference(definition_unfolding,[],[f14,f23,f23])).
% 0.76/0.60  fof(f23,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.76/0.60    inference(definition_unfolding,[],[f17,f22])).
% 0.76/0.60  fof(f22,plain,(
% 0.76/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.76/0.60    inference(definition_unfolding,[],[f18,f21])).
% 0.76/0.60  fof(f21,plain,(
% 0.76/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.76/0.60    inference(definition_unfolding,[],[f19,f20])).
% 0.76/0.60  fof(f20,plain,(
% 0.76/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f7])).
% 0.76/0.60  fof(f7,axiom,(
% 0.76/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.76/0.60  fof(f19,plain,(
% 0.76/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f6])).
% 0.76/0.60  fof(f6,axiom,(
% 0.76/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.76/0.60  fof(f18,plain,(
% 0.76/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f5])).
% 0.76/0.60  fof(f5,axiom,(
% 0.76/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.76/0.60  fof(f17,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f4])).
% 0.76/0.60  fof(f4,axiom,(
% 0.76/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.76/0.60  fof(f14,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f1])).
% 0.76/0.60  fof(f1,axiom,(
% 0.76/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.76/0.60  fof(f52,plain,(
% 0.76/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK1,sK2)),
% 0.76/0.60    inference(superposition,[],[f35,f27])).
% 0.76/0.60  fof(f27,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X2,X0,X3)) )),
% 0.76/0.60    inference(definition_unfolding,[],[f16,f23,f23])).
% 0.76/0.60  fof(f16,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f3])).
% 0.76/0.60  fof(f3,axiom,(
% 0.76/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_enumset1)).
% 0.76/0.60  fof(f35,plain,(
% 0.76/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK3,sK2)),
% 0.76/0.60    inference(superposition,[],[f24,f26])).
% 0.76/0.60  fof(f26,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X2,X1)) )),
% 0.76/0.60    inference(definition_unfolding,[],[f15,f23,f23])).
% 0.76/0.60  fof(f15,plain,(
% 0.76/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f2])).
% 0.76/0.60  fof(f2,axiom,(
% 0.76/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.76/0.60  fof(f24,plain,(
% 0.76/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK0)),
% 0.76/0.60    inference(definition_unfolding,[],[f13,f23,f23])).
% 0.76/0.60  fof(f13,plain,(
% 0.76/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.76/0.60    inference(cnf_transformation,[],[f12])).
% 0.76/0.60  fof(f12,plain,(
% 0.76/0.60    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.76/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).
% 0.76/0.60  fof(f11,plain,(
% 0.76/0.60    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.76/0.60    introduced(choice_axiom,[])).
% 0.76/0.60  fof(f10,plain,(
% 0.76/0.60    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0)),
% 0.76/0.60    inference(ennf_transformation,[],[f9])).
% 0.76/0.60  fof(f9,negated_conjecture,(
% 0.76/0.60    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.76/0.60    inference(negated_conjecture,[],[f8])).
% 0.76/0.60  fof(f8,conjecture,(
% 0.76/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).
% 0.76/0.60  % SZS output end Proof for theBenchmark
% 0.76/0.60  % (19014)------------------------------
% 0.76/0.60  % (19014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.76/0.60  % (19014)Termination reason: Refutation
% 0.76/0.60  
% 0.76/0.60  % (19014)Memory used [KB]: 1663
% 0.76/0.60  % (19014)Time elapsed: 0.027 s
% 0.76/0.60  % (19014)------------------------------
% 0.76/0.60  % (19014)------------------------------
% 0.76/0.61  % (18847)Success in time 0.247 s
%------------------------------------------------------------------------------

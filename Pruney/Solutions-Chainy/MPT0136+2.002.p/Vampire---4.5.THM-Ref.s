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
% DateTime   : Thu Dec  3 12:33:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  35 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  36 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f21,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))) ),
    inference(backward_demodulation,[],[f20,f13])).

fof(f20,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) ),
    inference(definition_unfolding,[],[f11,f19,f12,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f14,f12,f12])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) ),
    inference(definition_unfolding,[],[f16,f18])).

% (14323)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f11,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:02:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (824049664)
% 0.14/0.37  ipcrm: permission denied for id (824082433)
% 0.14/0.38  ipcrm: permission denied for id (824115203)
% 0.14/0.38  ipcrm: permission denied for id (826834948)
% 0.14/0.38  ipcrm: permission denied for id (826933255)
% 0.14/0.38  ipcrm: permission denied for id (826966024)
% 0.14/0.38  ipcrm: permission denied for id (826998793)
% 0.14/0.38  ipcrm: permission denied for id (827031562)
% 0.14/0.39  ipcrm: permission denied for id (827064331)
% 0.14/0.39  ipcrm: permission denied for id (827129869)
% 0.14/0.39  ipcrm: permission denied for id (824410126)
% 0.14/0.39  ipcrm: permission denied for id (824442895)
% 0.14/0.39  ipcrm: permission denied for id (827228177)
% 0.14/0.39  ipcrm: permission denied for id (827260946)
% 0.14/0.40  ipcrm: permission denied for id (827326484)
% 0.14/0.40  ipcrm: permission denied for id (824508437)
% 0.14/0.40  ipcrm: permission denied for id (827359254)
% 0.14/0.40  ipcrm: permission denied for id (824606744)
% 0.14/0.40  ipcrm: permission denied for id (827424793)
% 0.14/0.41  ipcrm: permission denied for id (824672283)
% 0.22/0.41  ipcrm: permission denied for id (824705052)
% 0.22/0.41  ipcrm: permission denied for id (824770591)
% 0.22/0.41  ipcrm: permission denied for id (827555872)
% 0.22/0.41  ipcrm: permission denied for id (827588641)
% 0.22/0.41  ipcrm: permission denied for id (827621410)
% 0.22/0.42  ipcrm: permission denied for id (824868899)
% 0.22/0.42  ipcrm: permission denied for id (827654180)
% 0.22/0.42  ipcrm: permission denied for id (824901669)
% 0.22/0.42  ipcrm: permission denied for id (827686950)
% 0.22/0.42  ipcrm: permission denied for id (827752488)
% 0.22/0.42  ipcrm: permission denied for id (827818026)
% 0.22/0.43  ipcrm: permission denied for id (825098284)
% 0.22/0.43  ipcrm: permission denied for id (825131054)
% 0.22/0.43  ipcrm: permission denied for id (825163823)
% 0.22/0.43  ipcrm: permission denied for id (827981874)
% 0.22/0.44  ipcrm: permission denied for id (825229364)
% 0.22/0.44  ipcrm: permission denied for id (828080181)
% 0.22/0.44  ipcrm: permission denied for id (828112950)
% 0.22/0.44  ipcrm: permission denied for id (828178488)
% 0.22/0.44  ipcrm: permission denied for id (828211257)
% 0.22/0.45  ipcrm: permission denied for id (828276795)
% 0.22/0.45  ipcrm: permission denied for id (828309564)
% 0.22/0.45  ipcrm: permission denied for id (828342333)
% 0.22/0.45  ipcrm: permission denied for id (825425982)
% 0.22/0.45  ipcrm: permission denied for id (825458751)
% 0.22/0.45  ipcrm: permission denied for id (828407873)
% 0.22/0.45  ipcrm: permission denied for id (825524290)
% 0.22/0.46  ipcrm: permission denied for id (828440643)
% 0.22/0.46  ipcrm: permission denied for id (828506181)
% 0.22/0.46  ipcrm: permission denied for id (828571719)
% 0.22/0.47  ipcrm: permission denied for id (828801102)
% 0.22/0.47  ipcrm: permission denied for id (825786447)
% 0.22/0.47  ipcrm: permission denied for id (828833872)
% 0.22/0.47  ipcrm: permission denied for id (825851985)
% 0.22/0.48  ipcrm: permission denied for id (828932180)
% 0.22/0.48  ipcrm: permission denied for id (825950293)
% 0.22/0.48  ipcrm: permission denied for id (825983063)
% 0.22/0.48  ipcrm: permission denied for id (826015832)
% 0.22/0.48  ipcrm: permission denied for id (829063258)
% 0.22/0.49  ipcrm: permission denied for id (826048603)
% 0.22/0.49  ipcrm: permission denied for id (829096028)
% 0.22/0.49  ipcrm: permission denied for id (829128797)
% 0.22/0.49  ipcrm: permission denied for id (826114142)
% 0.22/0.49  ipcrm: permission denied for id (826146911)
% 0.22/0.49  ipcrm: permission denied for id (826179680)
% 0.22/0.49  ipcrm: permission denied for id (826212449)
% 0.22/0.49  ipcrm: permission denied for id (826245218)
% 0.22/0.50  ipcrm: permission denied for id (829194340)
% 0.22/0.50  ipcrm: permission denied for id (826310757)
% 0.22/0.50  ipcrm: permission denied for id (829325417)
% 0.22/0.50  ipcrm: permission denied for id (829390955)
% 0.22/0.51  ipcrm: permission denied for id (829456493)
% 0.22/0.51  ipcrm: permission denied for id (829489262)
% 0.22/0.51  ipcrm: permission denied for id (826409071)
% 0.22/0.51  ipcrm: permission denied for id (826441841)
% 0.22/0.51  ipcrm: permission denied for id (829554802)
% 0.22/0.51  ipcrm: permission denied for id (829587571)
% 0.22/0.52  ipcrm: permission denied for id (829620340)
% 0.22/0.52  ipcrm: permission denied for id (826540150)
% 0.22/0.52  ipcrm: permission denied for id (826572919)
% 0.22/0.52  ipcrm: permission denied for id (826605688)
% 0.22/0.52  ipcrm: permission denied for id (826703993)
% 0.22/0.52  ipcrm: permission denied for id (829685882)
% 0.22/0.53  ipcrm: permission denied for id (829751420)
% 0.22/0.53  ipcrm: permission denied for id (829784189)
% 0.22/0.53  ipcrm: permission denied for id (826671230)
% 0.22/0.60  % (14321)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.60  % (14321)Refutation found. Thanks to Tanya!
% 0.22/0.60  % SZS status Theorem for theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(subsumption_resolution,[],[f21,f13])).
% 0.22/0.60  fof(f13,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),
% 0.22/0.60    inference(backward_demodulation,[],[f20,f13])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),
% 0.22/0.60    inference(definition_unfolding,[],[f11,f19,f12,f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.22/0.60    inference(definition_unfolding,[],[f14,f12,f12])).
% 0.22/0.60  fof(f14,plain,(
% 0.22/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.60  fof(f12,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.60  fof(f19,plain,(
% 0.22/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))))) )),
% 0.22/0.60    inference(definition_unfolding,[],[f16,f18])).
% 0.22/0.60  % (14323)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))))) )),
% 0.22/0.60    inference(definition_unfolding,[],[f15,f17])).
% 0.22/0.60  fof(f15,plain,(
% 0.22/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.60  fof(f11,plain,(
% 0.22/0.60    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.22/0.60    inference(cnf_transformation,[],[f10])).
% 0.22/0.60  fof(f10,plain,(
% 0.22/0.60    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).
% 0.22/0.60  fof(f9,plain,(
% 0.22/0.60    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f8,plain,(
% 0.22/0.60    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.22/0.60    inference(ennf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,negated_conjecture,(
% 0.22/0.60    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.22/0.60    inference(negated_conjecture,[],[f6])).
% 0.22/0.60  fof(f6,conjecture,(
% 0.22/0.60    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (14321)------------------------------
% 0.22/0.60  % (14321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (14321)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (14321)Memory used [KB]: 10490
% 0.22/0.60  % (14321)Time elapsed: 0.005 s
% 0.22/0.60  % (14321)------------------------------
% 0.22/0.60  % (14321)------------------------------
% 0.22/0.61  % (14163)Success in time 0.24 s
%------------------------------------------------------------------------------

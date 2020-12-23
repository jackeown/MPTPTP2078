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
% DateTime   : Thu Dec  3 12:33:11 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   34 (  62 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :   35 (  63 expanded)
%              Number of equality atoms :   34 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) ),
    inference(forward_demodulation,[],[f35,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f35,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))) ),
    inference(forward_demodulation,[],[f34,f15])).

fof(f34,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) ),
    inference(superposition,[],[f30,f15])).

fof(f30,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(forward_demodulation,[],[f29,f15])).

fof(f29,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(forward_demodulation,[],[f28,f15])).

fof(f28,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) ),
    inference(forward_demodulation,[],[f27,f15])).

fof(f27,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))))) ),
    inference(forward_demodulation,[],[f26,f15])).

fof(f26,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5)))) ),
    inference(forward_demodulation,[],[f25,f15])).

fof(f25,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) ),
    inference(forward_demodulation,[],[f24,f15])).

fof(f24,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)) ),
    inference(backward_demodulation,[],[f23,f15])).

fof(f23,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)) ),
    inference(definition_unfolding,[],[f12,f22,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

% (4883)Refutation not found, incomplete strategy% (4883)------------------------------
% (4883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4883)Termination reason: Refutation not found, incomplete strategy

% (4883)Memory used [KB]: 10490
% (4883)Time elapsed: 0.050 s
% (4883)------------------------------
% (4883)------------------------------
fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) ),
    inference(definition_unfolding,[],[f18,f20,f13])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f12,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:19:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (783056897)
% 0.13/0.36  ipcrm: permission denied for id (783089666)
% 0.13/0.36  ipcrm: permission denied for id (783122435)
% 0.13/0.36  ipcrm: permission denied for id (782696452)
% 0.13/0.36  ipcrm: permission denied for id (783155205)
% 0.13/0.37  ipcrm: permission denied for id (783187974)
% 0.13/0.37  ipcrm: permission denied for id (783220743)
% 0.13/0.37  ipcrm: permission denied for id (783253512)
% 0.13/0.37  ipcrm: permission denied for id (783286281)
% 0.13/0.37  ipcrm: permission denied for id (788889610)
% 0.13/0.37  ipcrm: permission denied for id (783351819)
% 0.13/0.37  ipcrm: permission denied for id (789643276)
% 0.13/0.38  ipcrm: permission denied for id (783417357)
% 0.13/0.38  ipcrm: permission denied for id (788955150)
% 0.13/0.38  ipcrm: permission denied for id (782761999)
% 0.13/0.38  ipcrm: permission denied for id (788987920)
% 0.13/0.38  ipcrm: permission denied for id (787283985)
% 0.13/0.38  ipcrm: permission denied for id (787316754)
% 0.13/0.38  ipcrm: permission denied for id (789020691)
% 0.13/0.39  ipcrm: permission denied for id (789053460)
% 0.13/0.39  ipcrm: permission denied for id (787447830)
% 0.13/0.39  ipcrm: permission denied for id (789708823)
% 0.13/0.39  ipcrm: permission denied for id (787513368)
% 0.13/0.39  ipcrm: permission denied for id (783777817)
% 0.13/0.39  ipcrm: permission denied for id (783810586)
% 0.13/0.40  ipcrm: permission denied for id (783843355)
% 0.13/0.40  ipcrm: permission denied for id (783876124)
% 0.13/0.40  ipcrm: permission denied for id (783908893)
% 0.13/0.40  ipcrm: permission denied for id (784007198)
% 0.13/0.40  ipcrm: permission denied for id (789151775)
% 0.13/0.40  ipcrm: permission denied for id (782827552)
% 0.13/0.40  ipcrm: permission denied for id (784039969)
% 0.13/0.40  ipcrm: permission denied for id (784072738)
% 0.13/0.40  ipcrm: permission denied for id (784105507)
% 0.20/0.41  ipcrm: permission denied for id (784138276)
% 0.20/0.41  ipcrm: permission denied for id (784171045)
% 0.20/0.41  ipcrm: permission denied for id (784203814)
% 0.20/0.41  ipcrm: permission denied for id (784236583)
% 0.20/0.41  ipcrm: permission denied for id (784269352)
% 0.20/0.41  ipcrm: permission denied for id (784302121)
% 0.20/0.41  ipcrm: permission denied for id (784334890)
% 0.20/0.41  ipcrm: permission denied for id (784367659)
% 0.20/0.41  ipcrm: permission denied for id (789184556)
% 0.20/0.41  ipcrm: permission denied for id (787611693)
% 0.20/0.41  ipcrm: permission denied for id (787644462)
% 0.20/0.42  ipcrm: permission denied for id (787677231)
% 0.20/0.42  ipcrm: permission denied for id (787710000)
% 0.20/0.42  ipcrm: permission denied for id (787742769)
% 0.20/0.42  ipcrm: permission denied for id (787775538)
% 0.20/0.42  ipcrm: permission denied for id (784695347)
% 0.20/0.42  ipcrm: permission denied for id (787808308)
% 0.20/0.42  ipcrm: permission denied for id (787841077)
% 0.20/0.42  ipcrm: permission denied for id (782893110)
% 0.20/0.42  ipcrm: permission denied for id (787873847)
% 0.20/0.42  ipcrm: permission denied for id (784793656)
% 0.20/0.42  ipcrm: permission denied for id (787906617)
% 0.20/0.43  ipcrm: permission denied for id (784859194)
% 0.20/0.43  ipcrm: permission denied for id (789217339)
% 0.20/0.43  ipcrm: permission denied for id (784924732)
% 0.20/0.43  ipcrm: permission denied for id (787972157)
% 0.20/0.43  ipcrm: permission denied for id (784990270)
% 0.20/0.43  ipcrm: permission denied for id (788004927)
% 0.20/0.43  ipcrm: permission denied for id (785055808)
% 0.20/0.43  ipcrm: permission denied for id (785088577)
% 0.20/0.44  ipcrm: permission denied for id (782925891)
% 0.20/0.44  ipcrm: permission denied for id (785154116)
% 0.20/0.44  ipcrm: permission denied for id (785219654)
% 0.20/0.44  ipcrm: permission denied for id (785252423)
% 0.20/0.44  ipcrm: permission denied for id (785285192)
% 0.20/0.44  ipcrm: permission denied for id (789807177)
% 0.20/0.44  ipcrm: permission denied for id (785350730)
% 0.20/0.44  ipcrm: permission denied for id (785383499)
% 0.20/0.45  ipcrm: permission denied for id (788136012)
% 0.20/0.45  ipcrm: permission denied for id (788168781)
% 0.20/0.45  ipcrm: permission denied for id (788201550)
% 0.20/0.45  ipcrm: permission denied for id (789839951)
% 0.20/0.45  ipcrm: permission denied for id (785547344)
% 0.20/0.45  ipcrm: permission denied for id (788267089)
% 0.20/0.45  ipcrm: permission denied for id (785612882)
% 0.20/0.45  ipcrm: permission denied for id (785645651)
% 0.20/0.46  ipcrm: permission denied for id (788299860)
% 0.20/0.46  ipcrm: permission denied for id (788332629)
% 0.20/0.46  ipcrm: permission denied for id (785743958)
% 0.20/0.46  ipcrm: permission denied for id (789413976)
% 0.20/0.46  ipcrm: permission denied for id (788430937)
% 0.20/0.46  ipcrm: permission denied for id (785875034)
% 0.20/0.46  ipcrm: permission denied for id (788463707)
% 0.20/0.47  ipcrm: permission denied for id (785940572)
% 0.20/0.47  ipcrm: permission denied for id (789446749)
% 0.20/0.47  ipcrm: permission denied for id (786006110)
% 0.20/0.47  ipcrm: permission denied for id (786038879)
% 0.20/0.47  ipcrm: permission denied for id (786071648)
% 0.20/0.47  ipcrm: permission denied for id (789479521)
% 0.20/0.47  ipcrm: permission denied for id (786137186)
% 0.20/0.48  ipcrm: permission denied for id (786169955)
% 0.20/0.48  ipcrm: permission denied for id (786202724)
% 0.20/0.48  ipcrm: permission denied for id (786235493)
% 0.20/0.48  ipcrm: permission denied for id (786268262)
% 0.20/0.48  ipcrm: permission denied for id (786301031)
% 0.20/0.48  ipcrm: permission denied for id (786333800)
% 0.20/0.48  ipcrm: permission denied for id (786366569)
% 0.20/0.48  ipcrm: permission denied for id (786399338)
% 0.20/0.49  ipcrm: permission denied for id (786432107)
% 0.20/0.49  ipcrm: permission denied for id (786464876)
% 0.20/0.49  ipcrm: permission denied for id (788594797)
% 0.20/0.49  ipcrm: permission denied for id (786530414)
% 0.20/0.49  ipcrm: permission denied for id (789512303)
% 0.20/0.49  ipcrm: permission denied for id (786595952)
% 0.20/0.49  ipcrm: permission denied for id (786628721)
% 0.20/0.49  ipcrm: permission denied for id (788660338)
% 0.20/0.50  ipcrm: permission denied for id (786694259)
% 0.20/0.50  ipcrm: permission denied for id (786727028)
% 0.20/0.50  ipcrm: permission denied for id (786792565)
% 0.20/0.50  ipcrm: permission denied for id (786825334)
% 0.20/0.50  ipcrm: permission denied for id (788693111)
% 0.20/0.50  ipcrm: permission denied for id (782991480)
% 0.20/0.50  ipcrm: permission denied for id (788725881)
% 0.20/0.51  ipcrm: permission denied for id (786923642)
% 0.20/0.51  ipcrm: permission denied for id (789938299)
% 0.20/0.51  ipcrm: permission denied for id (789971068)
% 0.20/0.51  ipcrm: permission denied for id (788824189)
% 0.20/0.51  ipcrm: permission denied for id (787054718)
% 0.20/0.51  ipcrm: permission denied for id (787087487)
% 0.96/0.61  % (4886)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.96/0.62  % (4883)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.96/0.62  % (4874)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.96/0.62  % (4886)Refutation found. Thanks to Tanya!
% 0.96/0.62  % SZS status Theorem for theBenchmark
% 0.96/0.62  % SZS output start Proof for theBenchmark
% 0.96/0.62  fof(f37,plain,(
% 0.96/0.62    $false),
% 0.96/0.62    inference(trivial_inequality_removal,[],[f36])).
% 0.96/0.62  fof(f36,plain,(
% 0.96/0.62    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))),
% 0.96/0.62    inference(forward_demodulation,[],[f35,f15])).
% 0.96/0.62  fof(f15,plain,(
% 0.96/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.96/0.62    inference(cnf_transformation,[],[f1])).
% 0.96/0.62  fof(f1,axiom,(
% 0.96/0.62    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.96/0.62  fof(f35,plain,(
% 0.96/0.62    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),
% 0.96/0.62    inference(forward_demodulation,[],[f34,f15])).
% 0.96/0.62  fof(f34,plain,(
% 0.96/0.62    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),
% 0.96/0.62    inference(superposition,[],[f30,f15])).
% 0.96/0.62  fof(f30,plain,(
% 0.96/0.62    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),
% 0.96/0.62    inference(forward_demodulation,[],[f29,f15])).
% 0.96/0.62  fof(f29,plain,(
% 0.96/0.62    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),
% 0.96/0.62    inference(forward_demodulation,[],[f28,f15])).
% 0.96/0.62  fof(f28,plain,(
% 0.96/0.62    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))),
% 0.96/0.62    inference(forward_demodulation,[],[f27,f15])).
% 0.96/0.62  fof(f27,plain,(
% 0.96/0.62    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5)))))),
% 0.96/0.62    inference(forward_demodulation,[],[f26,f15])).
% 0.96/0.62  fof(f26,plain,(
% 0.96/0.62    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))))),
% 0.96/0.62    inference(forward_demodulation,[],[f25,f15])).
% 0.96/0.62  fof(f25,plain,(
% 0.96/0.62    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5)))),
% 0.96/0.62    inference(forward_demodulation,[],[f24,f15])).
% 0.96/0.62  fof(f24,plain,(
% 0.96/0.62    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5))),
% 0.96/0.62    inference(backward_demodulation,[],[f23,f15])).
% 0.96/0.62  fof(f23,plain,(
% 0.96/0.62    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5))),
% 0.96/0.62    inference(definition_unfolding,[],[f12,f22,f21])).
% 0.96/0.62  fof(f21,plain,(
% 0.96/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4))) )),
% 0.96/0.62    inference(definition_unfolding,[],[f17,f20])).
% 0.96/0.62  fof(f20,plain,(
% 0.96/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3))) )),
% 0.96/0.62    inference(definition_unfolding,[],[f16,f19])).
% 0.96/0.62  fof(f19,plain,(
% 0.96/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 0.96/0.62    inference(definition_unfolding,[],[f14,f13])).
% 0.96/0.62  fof(f13,plain,(
% 0.96/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.96/0.62    inference(cnf_transformation,[],[f2])).
% 0.96/0.62  fof(f2,axiom,(
% 0.96/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.96/0.62  % (4883)Refutation not found, incomplete strategy% (4883)------------------------------
% 0.96/0.62  % (4883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.96/0.62  % (4883)Termination reason: Refutation not found, incomplete strategy
% 0.96/0.62  
% 0.96/0.62  % (4883)Memory used [KB]: 10490
% 0.96/0.62  % (4883)Time elapsed: 0.050 s
% 0.96/0.62  % (4883)------------------------------
% 0.96/0.62  % (4883)------------------------------
% 0.96/0.62  fof(f14,plain,(
% 0.96/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.96/0.62    inference(cnf_transformation,[],[f3])).
% 0.96/0.62  fof(f3,axiom,(
% 0.96/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.96/0.62  fof(f16,plain,(
% 0.96/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.96/0.62    inference(cnf_transformation,[],[f4])).
% 0.96/0.62  fof(f4,axiom,(
% 0.96/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.96/0.62  fof(f17,plain,(
% 0.96/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.96/0.62    inference(cnf_transformation,[],[f5])).
% 0.96/0.62  fof(f5,axiom,(
% 0.96/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.96/0.62  fof(f22,plain,(
% 0.96/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) )),
% 0.96/0.62    inference(definition_unfolding,[],[f18,f20,f13])).
% 0.96/0.62  fof(f18,plain,(
% 0.96/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.96/0.62    inference(cnf_transformation,[],[f6])).
% 0.96/0.62  fof(f6,axiom,(
% 0.96/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.96/0.62  fof(f12,plain,(
% 0.96/0.62    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 0.96/0.62    inference(cnf_transformation,[],[f11])).
% 0.96/0.62  fof(f11,plain,(
% 0.96/0.62    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 0.96/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).
% 0.96/0.62  fof(f10,plain,(
% 0.96/0.62    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 0.96/0.62    introduced(choice_axiom,[])).
% 0.96/0.62  fof(f9,plain,(
% 0.96/0.62    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.96/0.62    inference(ennf_transformation,[],[f8])).
% 0.96/0.62  fof(f8,negated_conjecture,(
% 0.96/0.62    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.96/0.62    inference(negated_conjecture,[],[f7])).
% 0.96/0.62  fof(f7,conjecture,(
% 0.96/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.96/0.62  % SZS output end Proof for theBenchmark
% 0.96/0.62  % (4886)------------------------------
% 0.96/0.62  % (4886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.96/0.62  % (4886)Termination reason: Refutation
% 0.96/0.62  
% 0.96/0.62  % (4886)Memory used [KB]: 6140
% 0.96/0.62  % (4886)Time elapsed: 0.049 s
% 0.96/0.62  % (4886)------------------------------
% 0.96/0.62  % (4886)------------------------------
% 0.96/0.62  % (4720)Success in time 0.269 s
%------------------------------------------------------------------------------

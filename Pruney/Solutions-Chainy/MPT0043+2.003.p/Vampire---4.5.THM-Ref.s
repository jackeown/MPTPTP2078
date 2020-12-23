%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,plain,(
    $false ),
    inference(resolution,[],[f14,f8])).

fof(f8,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(subsumption_resolution,[],[f13,f9])).

fof(f9,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f11,f10])).

fof(f10,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:46:34 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (808484865)
% 0.15/0.37  ipcrm: permission denied for id (808517634)
% 0.15/0.37  ipcrm: permission denied for id (808583172)
% 0.15/0.37  ipcrm: permission denied for id (808615941)
% 0.15/0.37  ipcrm: permission denied for id (808648711)
% 0.15/0.38  ipcrm: permission denied for id (808747020)
% 0.15/0.38  ipcrm: permission denied for id (808779789)
% 0.15/0.38  ipcrm: permission denied for id (808812558)
% 0.15/0.38  ipcrm: permission denied for id (808845327)
% 0.15/0.38  ipcrm: permission denied for id (808878096)
% 0.15/0.39  ipcrm: permission denied for id (808943634)
% 0.15/0.39  ipcrm: permission denied for id (809009172)
% 0.15/0.39  ipcrm: permission denied for id (809041941)
% 0.15/0.39  ipcrm: permission denied for id (809074710)
% 0.15/0.40  ipcrm: permission denied for id (809140248)
% 0.15/0.40  ipcrm: permission denied for id (809173017)
% 0.15/0.40  ipcrm: permission denied for id (809205786)
% 0.15/0.40  ipcrm: permission denied for id (809238555)
% 0.22/0.40  ipcrm: permission denied for id (809304093)
% 0.22/0.40  ipcrm: permission denied for id (809336863)
% 0.22/0.40  ipcrm: permission denied for id (809369632)
% 0.22/0.41  ipcrm: permission denied for id (809467939)
% 0.22/0.41  ipcrm: permission denied for id (809500708)
% 0.22/0.41  ipcrm: permission denied for id (809566247)
% 0.22/0.41  ipcrm: permission denied for id (809631785)
% 0.22/0.41  ipcrm: permission denied for id (809697323)
% 0.22/0.42  ipcrm: permission denied for id (809730092)
% 0.22/0.42  ipcrm: permission denied for id (809762861)
% 0.22/0.42  ipcrm: permission denied for id (809828400)
% 0.22/0.42  ipcrm: permission denied for id (809861169)
% 0.22/0.43  ipcrm: permission denied for id (809926709)
% 0.22/0.43  ipcrm: permission denied for id (809959478)
% 0.22/0.43  ipcrm: permission denied for id (810057785)
% 0.22/0.43  ipcrm: permission denied for id (810123322)
% 0.22/0.43  ipcrm: permission denied for id (810188860)
% 0.22/0.44  ipcrm: permission denied for id (810254399)
% 0.22/0.44  ipcrm: permission denied for id (810352706)
% 0.22/0.44  ipcrm: permission denied for id (810418244)
% 0.22/0.44  ipcrm: permission denied for id (810451014)
% 0.22/0.45  ipcrm: permission denied for id (810582090)
% 0.22/0.45  ipcrm: permission denied for id (810614859)
% 0.22/0.45  ipcrm: permission denied for id (810647628)
% 0.22/0.45  ipcrm: permission denied for id (810680397)
% 0.22/0.46  ipcrm: permission denied for id (810745937)
% 0.22/0.46  ipcrm: permission denied for id (810778706)
% 0.22/0.46  ipcrm: permission denied for id (810811475)
% 0.22/0.46  ipcrm: permission denied for id (810844244)
% 0.22/0.46  ipcrm: permission denied for id (810877013)
% 0.22/0.47  ipcrm: permission denied for id (810975320)
% 0.22/0.47  ipcrm: permission denied for id (811008090)
% 0.22/0.47  ipcrm: permission denied for id (811040859)
% 0.22/0.47  ipcrm: permission denied for id (811073628)
% 0.22/0.47  ipcrm: permission denied for id (811106397)
% 0.22/0.47  ipcrm: permission denied for id (811139167)
% 0.22/0.47  ipcrm: permission denied for id (811171936)
% 0.22/0.48  ipcrm: permission denied for id (811204705)
% 0.22/0.48  ipcrm: permission denied for id (811270244)
% 0.22/0.48  ipcrm: permission denied for id (811368551)
% 0.22/0.48  ipcrm: permission denied for id (811401320)
% 0.22/0.48  ipcrm: permission denied for id (811434089)
% 0.22/0.49  ipcrm: permission denied for id (811597934)
% 0.22/0.49  ipcrm: permission denied for id (811663472)
% 0.22/0.49  ipcrm: permission denied for id (811729010)
% 0.22/0.49  ipcrm: permission denied for id (811761779)
% 0.22/0.50  ipcrm: permission denied for id (811827318)
% 0.22/0.50  ipcrm: permission denied for id (811860087)
% 0.22/0.50  ipcrm: permission denied for id (811892856)
% 0.22/0.50  ipcrm: permission denied for id (811958394)
% 0.22/0.50  ipcrm: permission denied for id (812023933)
% 0.22/0.58  % (23698)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (23698)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(resolution,[],[f14,f8])).
% 0.22/0.58  fof(f8,plain,(
% 0.22/0.58    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,plain,(
% 0.22/0.58    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.58    inference(negated_conjecture,[],[f4])).
% 0.22/0.58  fof(f4,conjecture,(
% 0.22/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f13,f9])).
% 0.22/0.58  fof(f9,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | ~r1_tarski(k1_xboole_0,X1)) )),
% 0.22/0.58    inference(superposition,[],[f11,f10])).
% 0.22/0.58  fof(f10,plain,(
% 0.22/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (23698)------------------------------
% 0.22/0.58  % (23698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (23698)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (23698)Memory used [KB]: 10490
% 0.22/0.58  % (23698)Time elapsed: 0.005 s
% 0.22/0.58  % (23698)------------------------------
% 0.22/0.58  % (23698)------------------------------
% 0.22/0.58  % (23531)Success in time 0.224 s
%------------------------------------------------------------------------------

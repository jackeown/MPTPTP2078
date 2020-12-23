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
% DateTime   : Thu Dec  3 12:34:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) ),
    inference(superposition,[],[f8,f9])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (814514178)
% 0.13/0.37  ipcrm: permission denied for id (813957123)
% 0.13/0.37  ipcrm: permission denied for id (814546948)
% 0.13/0.37  ipcrm: permission denied for id (814612486)
% 0.13/0.37  ipcrm: permission denied for id (814645255)
% 0.13/0.38  ipcrm: permission denied for id (814710793)
% 0.13/0.38  ipcrm: permission denied for id (814743562)
% 0.13/0.38  ipcrm: permission denied for id (814776331)
% 0.13/0.38  ipcrm: permission denied for id (813989901)
% 0.13/0.39  ipcrm: permission denied for id (814907408)
% 0.13/0.39  ipcrm: permission denied for id (814940177)
% 0.13/0.39  ipcrm: permission denied for id (814972946)
% 0.13/0.39  ipcrm: permission denied for id (815038484)
% 0.13/0.39  ipcrm: permission denied for id (815136791)
% 0.13/0.40  ipcrm: permission denied for id (815202329)
% 0.13/0.41  ipcrm: permission denied for id (815464481)
% 0.13/0.41  ipcrm: permission denied for id (815530019)
% 0.13/0.41  ipcrm: permission denied for id (815562788)
% 0.13/0.41  ipcrm: permission denied for id (815661095)
% 0.13/0.42  ipcrm: permission denied for id (815726633)
% 0.13/0.42  ipcrm: permission denied for id (815759402)
% 0.13/0.42  ipcrm: permission denied for id (814121006)
% 0.21/0.42  ipcrm: permission denied for id (815923248)
% 0.21/0.43  ipcrm: permission denied for id (815956017)
% 0.21/0.43  ipcrm: permission denied for id (816021555)
% 0.21/0.43  ipcrm: permission denied for id (816119862)
% 0.21/0.43  ipcrm: permission denied for id (816152631)
% 0.21/0.43  ipcrm: permission denied for id (816185400)
% 0.21/0.44  ipcrm: permission denied for id (816283707)
% 0.21/0.45  ipcrm: permission denied for id (816513090)
% 0.21/0.45  ipcrm: permission denied for id (816578628)
% 0.21/0.45  ipcrm: permission denied for id (816676935)
% 0.21/0.45  ipcrm: permission denied for id (816742473)
% 0.21/0.45  ipcrm: permission denied for id (816775242)
% 0.21/0.46  ipcrm: permission denied for id (814186572)
% 0.21/0.46  ipcrm: permission denied for id (814219341)
% 0.21/0.46  ipcrm: permission denied for id (816840782)
% 0.21/0.46  ipcrm: permission denied for id (814284879)
% 0.21/0.46  ipcrm: permission denied for id (816939090)
% 0.21/0.47  ipcrm: permission denied for id (816971859)
% 0.21/0.47  ipcrm: permission denied for id (817135704)
% 0.21/0.47  ipcrm: permission denied for id (817201242)
% 0.21/0.48  ipcrm: permission denied for id (817266780)
% 0.21/0.48  ipcrm: permission denied for id (814317666)
% 0.21/0.49  ipcrm: permission denied for id (817561702)
% 0.21/0.49  ipcrm: permission denied for id (817594471)
% 0.21/0.49  ipcrm: permission denied for id (817627240)
% 0.21/0.49  ipcrm: permission denied for id (817660009)
% 0.21/0.50  ipcrm: permission denied for id (817791085)
% 0.21/0.50  ipcrm: permission denied for id (817922161)
% 0.21/0.50  ipcrm: permission denied for id (817954930)
% 0.21/0.50  ipcrm: permission denied for id (817987699)
% 0.21/0.50  ipcrm: permission denied for id (818053236)
% 0.21/0.51  ipcrm: permission denied for id (818282619)
% 0.21/0.51  ipcrm: permission denied for id (818315388)
% 0.21/0.51  ipcrm: permission denied for id (818348157)
% 0.21/0.51  ipcrm: permission denied for id (818380926)
% 0.21/0.52  ipcrm: permission denied for id (818413695)
% 0.21/0.57  % (29300)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.57  % (29300)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f11,f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)),
% 0.21/0.57    inference(superposition,[],[f8,f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.21/0.57  fof(f6,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f5,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.57    inference(negated_conjecture,[],[f3])).
% 0.21/0.57  fof(f3,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (29300)------------------------------
% 0.21/0.57  % (29300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29300)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (29300)Memory used [KB]: 6012
% 0.21/0.57  % (29300)Time elapsed: 0.002 s
% 0.21/0.57  % (29300)------------------------------
% 0.21/0.57  % (29300)------------------------------
% 0.21/0.57  % (29164)Success in time 0.208 s
%------------------------------------------------------------------------------

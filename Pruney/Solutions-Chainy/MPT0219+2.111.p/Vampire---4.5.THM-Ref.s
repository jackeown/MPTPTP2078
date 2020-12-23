%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   12 (  15 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  25 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f10,f9,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(k1_tarski(X1),k1_tarski(X2))
      | X1 = X2 ) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( X1 = X2
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f9,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f10,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 20:34:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.49  % (20472)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.50  % (20482)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.50  % (20474)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.50  % (20474)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f10,f9,f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) | X1 = X2) )),
% 0.23/0.50    inference(definition_unfolding,[],[f14,f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_tarski(X1,X2) | X1 = X2) )),
% 0.23/0.50    inference(cnf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (X1 = X2 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 0.23/0.50    inference(ennf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.23/0.50  fof(f9,plain,(
% 0.23/0.50    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.50    inference(cnf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,plain,(
% 0.23/0.50    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.50    inference(ennf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.50    inference(negated_conjecture,[],[f5])).
% 0.23/0.50  fof(f5,conjecture,(
% 0.23/0.50    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    sK0 != sK1),
% 0.23/0.50    inference(cnf_transformation,[],[f7])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (20474)------------------------------
% 0.23/0.50  % (20474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (20474)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (20474)Memory used [KB]: 6140
% 0.23/0.50  % (20474)Time elapsed: 0.046 s
% 0.23/0.50  % (20474)------------------------------
% 0.23/0.50  % (20474)------------------------------
% 0.23/0.51  % (20454)Success in time 0.133 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:29:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  23 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_xboole_0 != sK0
    & k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != X0
        & k2_xboole_0(X0,X1) = k1_xboole_0 )
   => ( k1_xboole_0 != sK0
      & k1_xboole_0 = k2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & k2_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = k1_xboole_0
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f23,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,(
    r1_tarski(sK0,k1_xboole_0) ),
    inference(superposition,[],[f13,f10])).

fof(f10,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f18,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f14,f12])).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (20108)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (20116)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (20116)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f23,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    k1_xboole_0 != sK0),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k1_xboole_0 != sK0 & k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 != X0 & k2_xboole_0(X0,X1) = k1_xboole_0) => (k1_xboole_0 != sK0 & k1_xboole_0 = k2_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 != X0 & k2_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    k1_xboole_0 = sK0),
% 0.21/0.46    inference(resolution,[],[f18,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    r1_tarski(sK0,k1_xboole_0)),
% 0.21/0.46    inference(superposition,[],[f13,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(superposition,[],[f14,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (20116)------------------------------
% 0.21/0.46  % (20116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (20116)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (20116)Memory used [KB]: 1535
% 0.21/0.46  % (20116)Time elapsed: 0.056 s
% 0.21/0.46  % (20116)------------------------------
% 0.21/0.46  % (20116)------------------------------
% 0.21/0.46  % (20097)Success in time 0.108 s
%------------------------------------------------------------------------------

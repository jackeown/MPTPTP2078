%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  25 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   26 (  33 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f14])).

fof(f14,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f25,plain,(
    r2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f12,f22])).

fof(f22,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f19,f13])).

fof(f13,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f19,plain,(
    ~ r2_xboole_0(k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f12,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f12,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] : r2_xboole_0(X0,k1_xboole_0)
   => r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (19228)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  % (19228)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f25,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.20/0.42    inference(rectify,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    r2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.42    inference(backward_demodulation,[],[f12,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    k1_xboole_0 = sK0),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f19,f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ~r2_xboole_0(k1_xboole_0,sK0)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f12,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    r2_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    r2_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0] : r2_xboole_0(X0,k1_xboole_0) => r2_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0] : r2_xboole_0(X0,k1_xboole_0)),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (19228)------------------------------
% 0.20/0.42  % (19228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (19228)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (19228)Memory used [KB]: 6012
% 0.20/0.42  % (19228)Time elapsed: 0.004 s
% 0.20/0.42  % (19228)------------------------------
% 0.20/0.42  % (19228)------------------------------
% 0.20/0.42  % (19225)Success in time 0.063 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  25 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  45 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f13])).

fof(f13,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f26,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f8,f19])).

fof(f19,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f14,f15])).

fof(f15,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f8,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).

fof(f14,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f7,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f8,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (24891)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.41  % (24891)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(subsumption_resolution,[],[f26,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.41    inference(equality_resolution,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    r2_xboole_0(sK0,sK0)),
% 0.21/0.41    inference(backward_demodulation,[],[f8,f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    sK0 = sK1),
% 0.21/0.41    inference(resolution,[],[f14,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ~r2_xboole_0(sK0,sK1)),
% 0.21/0.41    inference(resolution,[],[f8,f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    r2_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.21/0.41    inference(resolution,[],[f7,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    r1_tarski(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,plain,(
% 0.21/0.41    ? [X0,X1] : (r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.41    inference(negated_conjecture,[],[f3])).
% 0.21/0.41  fof(f3,conjecture,(
% 0.21/0.41    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    r2_xboole_0(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f5])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (24891)------------------------------
% 0.21/0.41  % (24891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (24891)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (24891)Memory used [KB]: 1535
% 0.21/0.41  % (24891)Time elapsed: 0.003 s
% 0.21/0.41  % (24891)------------------------------
% 0.21/0.41  % (24891)------------------------------
% 0.21/0.41  % (24877)Success in time 0.054 s
%------------------------------------------------------------------------------

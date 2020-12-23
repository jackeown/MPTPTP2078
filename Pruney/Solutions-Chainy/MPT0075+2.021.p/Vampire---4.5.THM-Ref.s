%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  56 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 177 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f15,f45])).

fof(f45,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f44,f42])).

fof(f42,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f29,f17])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r1_xboole_0(sK0,sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK2,sK0)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK0,sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK2,sK0)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_xboole_0(X0,sK0) ) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f28,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f25,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2,X0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f16,f23])).

fof(f16,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (29681)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.43  % (29681)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f46,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(backward_demodulation,[],[f15,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    k1_xboole_0 = sK2),
% 0.21/0.43    inference(subsumption_resolution,[],[f44,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK0)),
% 0.21/0.43    inference(resolution,[],[f29,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    r1_tarski(sK2,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 0.21/0.43    inference(flattening,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_xboole_0(X0,sK0)) )),
% 0.21/0.43    inference(resolution,[],[f28,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK0)),
% 0.21/0.43    inference(resolution,[],[f18,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    k1_xboole_0 = sK2 | ~r1_xboole_0(sK2,sK0)),
% 0.21/0.43    inference(resolution,[],[f31,f22])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK2) | k1_xboole_0 = sK2),
% 0.21/0.43    inference(resolution,[],[f25,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(sK2,X0) | ~r1_xboole_0(sK0,X0)) )),
% 0.21/0.43    inference(resolution,[],[f16,f23])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    r1_tarski(sK2,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ~v1_xboole_0(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (29681)------------------------------
% 0.21/0.43  % (29681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (29681)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (29681)Memory used [KB]: 1663
% 0.21/0.43  % (29681)Time elapsed: 0.026 s
% 0.21/0.43  % (29681)------------------------------
% 0.21/0.43  % (29681)------------------------------
% 0.21/0.43  % (29676)Success in time 0.073 s
%------------------------------------------------------------------------------

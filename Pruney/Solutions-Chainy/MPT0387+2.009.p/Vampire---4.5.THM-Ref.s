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
% DateTime   : Thu Dec  3 12:45:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  62 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(global_subsumption,[],[f15,f23])).

fof(f23,plain,(
    k1_xboole_0 = k1_setfam_1(sK0) ),
    inference(resolution,[],[f22,f14])).

fof(f14,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != k1_setfam_1(sK0)
    & r2_hidden(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        & r2_hidden(k1_xboole_0,X0) )
   => ( k1_xboole_0 != k1_setfam_1(sK0)
      & r2_hidden(k1_xboole_0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f22,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_setfam_1(X0),X1)
      | k1_xboole_0 = k1_setfam_1(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f18,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f15,plain,(
    k1_xboole_0 != k1_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (8311)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.40  % (8311)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f24,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(global_subsumption,[],[f15,f23])).
% 0.20/0.40  fof(f23,plain,(
% 0.20/0.40    k1_xboole_0 = k1_setfam_1(sK0)),
% 0.20/0.40    inference(resolution,[],[f22,f14])).
% 0.20/0.40  fof(f14,plain,(
% 0.20/0.40    r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.40    inference(cnf_transformation,[],[f13])).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    k1_xboole_0 != k1_setfam_1(sK0) & r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0)) => (k1_xboole_0 != k1_setfam_1(sK0) & r2_hidden(k1_xboole_0,sK0))),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.40  fof(f7,plain,(
% 0.20/0.40    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0))),
% 0.20/0.40    inference(ennf_transformation,[],[f6])).
% 0.20/0.40  fof(f6,negated_conjecture,(
% 0.20/0.40    ~! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.20/0.40    inference(negated_conjecture,[],[f5])).
% 0.20/0.40  fof(f5,conjecture,(
% 0.20/0.40    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).
% 0.20/0.40  fof(f22,plain,(
% 0.20/0.40    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k1_setfam_1(X0)) )),
% 0.20/0.40    inference(resolution,[],[f21,f16])).
% 0.20/0.40  fof(f16,plain,(
% 0.20/0.40    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.40  fof(f21,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_xboole_0(k1_setfam_1(X0),X1) | k1_xboole_0 = k1_setfam_1(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.40    inference(resolution,[],[f20,f19])).
% 0.20/0.40  fof(f19,plain,(
% 0.20/0.40    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f11])).
% 0.20/0.40  fof(f11,plain,(
% 0.20/0.40    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f4])).
% 0.20/0.40  fof(f4,axiom,(
% 0.20/0.40    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.40  fof(f20,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = X0) )),
% 0.20/0.40    inference(resolution,[],[f18,f17])).
% 0.20/0.40  fof(f17,plain,(
% 0.20/0.40    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.40    inference(cnf_transformation,[],[f8])).
% 0.20/0.40  fof(f8,plain,(
% 0.20/0.40    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.40    inference(ennf_transformation,[],[f1])).
% 0.20/0.40  fof(f1,axiom,(
% 0.20/0.40    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.40  fof(f18,plain,(
% 0.20/0.40    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f10])).
% 0.20/0.40  fof(f10,plain,(
% 0.20/0.40    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.40    inference(flattening,[],[f9])).
% 0.20/0.40  fof(f9,plain,(
% 0.20/0.40    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.40  fof(f15,plain,(
% 0.20/0.40    k1_xboole_0 != k1_setfam_1(sK0)),
% 0.20/0.40    inference(cnf_transformation,[],[f13])).
% 0.20/0.40  % SZS output end Proof for theBenchmark
% 0.20/0.40  % (8311)------------------------------
% 0.20/0.40  % (8311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.40  % (8311)Termination reason: Refutation
% 0.20/0.40  
% 0.20/0.40  % (8311)Memory used [KB]: 6012
% 0.20/0.40  % (8311)Time elapsed: 0.003 s
% 0.20/0.40  % (8311)------------------------------
% 0.20/0.40  % (8311)------------------------------
% 0.20/0.40  % (8306)Success in time 0.046 s
%------------------------------------------------------------------------------

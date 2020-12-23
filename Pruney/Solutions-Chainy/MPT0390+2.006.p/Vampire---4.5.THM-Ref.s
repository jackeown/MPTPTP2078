%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  35 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  91 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(global_subsumption,[],[f14,f25])).

fof(f25,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f24,f15])).

fof(f15,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
    & r1_tarski(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_setfam_1(X1),X2)
        & r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
      & r1_tarski(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f24,plain,(
    ! [X0] :
      ( r1_tarski(k1_setfam_1(sK1),X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f18,f23])).

fof(f23,plain,(
    sK0 = k2_xboole_0(k1_setfam_1(sK1),sK0) ),
    inference(resolution,[],[f21,f13])).

fof(f13,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k2_xboole_0(k1_setfam_1(X0),X1) = X1 ) ),
    inference(resolution,[],[f17,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f14,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (2845)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (2845)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(global_subsumption,[],[f14,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ~r1_tarski(sK0,sK2)),
% 0.21/0.41    inference(resolution,[],[f24,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ~r1_tarski(k1_setfam_1(sK1),sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ~r1_tarski(k1_setfam_1(sK1),sK2) & r1_tarski(sK0,sK2) & r2_hidden(sK0,sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1)) => (~r1_tarski(k1_setfam_1(sK1),sK2) & r1_tarski(sK0,sK2) & r2_hidden(sK0,sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1))),
% 0.21/0.41    inference(flattening,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & (r1_tarski(X0,X2) & r2_hidden(X0,X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.21/0.41    inference(negated_conjecture,[],[f4])).
% 0.21/0.41  fof(f4,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(k1_setfam_1(sK1),X0) | ~r1_tarski(sK0,X0)) )),
% 0.21/0.41    inference(superposition,[],[f18,f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    sK0 = k2_xboole_0(k1_setfam_1(sK1),sK0)),
% 0.21/0.41    inference(resolution,[],[f21,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    r2_hidden(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k2_xboole_0(k1_setfam_1(X0),X1) = X1) )),
% 0.21/0.41    inference(resolution,[],[f17,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    r1_tarski(sK0,sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (2845)------------------------------
% 0.21/0.41  % (2845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (2845)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (2845)Memory used [KB]: 6012
% 0.21/0.41  % (2845)Time elapsed: 0.005 s
% 0.21/0.41  % (2845)------------------------------
% 0.21/0.41  % (2845)------------------------------
% 0.21/0.42  % (2837)Success in time 0.065 s
%------------------------------------------------------------------------------

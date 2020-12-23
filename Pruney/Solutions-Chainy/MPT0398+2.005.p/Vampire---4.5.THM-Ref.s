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
% DateTime   : Thu Dec  3 12:46:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f9,f10,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f10,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f9,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).

fof(f7,plain,
    ( ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0)
   => ~ r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (26748)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (26750)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (26750)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f9,f10,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_setfam_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ~r1_setfam_1(k1_xboole_0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ~r1_setfam_1(k1_xboole_0,sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : ~r1_setfam_1(k1_xboole_0,X0) => ~r1_setfam_1(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0] : ~r1_setfam_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0] : r1_setfam_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0] : r1_setfam_1(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_setfam_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (26750)------------------------------
% 0.21/0.47  % (26750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26750)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (26750)Memory used [KB]: 5245
% 0.21/0.47  % (26750)Time elapsed: 0.004 s
% 0.21/0.47  % (26750)------------------------------
% 0.21/0.47  % (26750)------------------------------
% 0.21/0.47  % (26742)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (26732)Success in time 0.114 s
%------------------------------------------------------------------------------

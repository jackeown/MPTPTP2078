%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f12])).

fof(f12,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f15,plain,(
    r2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f14,f10])).

fof(f10,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_xboole_0(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f13,f11])).

fof(f11,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:17:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (11327)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (11327)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f15,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.21/0.47    inference(rectify,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    r2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    inference(resolution,[],[f14,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    r2_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : r2_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f13,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11327)------------------------------
% 0.21/0.47  % (11327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11327)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11327)Memory used [KB]: 5245
% 0.21/0.47  % (11327)Time elapsed: 0.053 s
% 0.21/0.47  % (11327)------------------------------
% 0.21/0.47  % (11327)------------------------------
% 0.21/0.47  % (11320)Success in time 0.109 s
%------------------------------------------------------------------------------

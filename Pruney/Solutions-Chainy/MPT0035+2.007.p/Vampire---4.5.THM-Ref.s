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
% DateTime   : Thu Dec  3 12:29:45 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   21 (  48 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 ( 132 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f20,f13,f14,f21,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK2(X0,X1,X2),X0)
        & r1_tarski(sK2(X0,X1,X2),X2)
        & r1_tarski(sK2(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK2(X0,X1,X2),X0)
        & r1_tarski(sK2(X0,X1,X2),X2)
        & r1_tarski(sK2(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f21,plain,(
    r1_tarski(sK2(sK0,sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f20,f13,f14,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X2),X1)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    sK0 != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(X0,X1) != X0
        & r1_tarski(X0,X1) )
   => ( sK0 != k3_xboole_0(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X0,X1) != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k3_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f16,f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:08:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.43  % (27827)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.43  % (27822)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.23/0.43  % (27820)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.23/0.43  % (27822)Refutation found. Thanks to Tanya!
% 0.23/0.43  % SZS status Theorem for theBenchmark
% 0.23/0.43  % SZS output start Proof for theBenchmark
% 0.23/0.43  fof(f27,plain,(
% 0.23/0.43    $false),
% 0.23/0.43    inference(unit_resulting_resolution,[],[f20,f13,f14,f21,f19])).
% 0.23/0.43  fof(f19,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (~r1_tarski(sK2(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f12])).
% 0.23/0.43  fof(f12,plain,(
% 0.23/0.43    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK2(X0,X1,X2),X0) & r1_tarski(sK2(X0,X1,X2),X2) & r1_tarski(sK2(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f11])).
% 0.23/0.43  fof(f11,plain,(
% 0.23/0.43    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK2(X0,X1,X2),X0) & r1_tarski(sK2(X0,X1,X2),X2) & r1_tarski(sK2(X0,X1,X2),X1)))),
% 0.23/0.43    introduced(choice_axiom,[])).
% 0.23/0.43  fof(f8,plain,(
% 0.23/0.43    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.43    inference(flattening,[],[f7])).
% 0.23/0.43  fof(f7,plain,(
% 0.23/0.43    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.43    inference(ennf_transformation,[],[f2])).
% 0.23/0.43  fof(f2,axiom,(
% 0.23/0.43    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.23/0.43  fof(f21,plain,(
% 0.23/0.43    r1_tarski(sK2(sK0,sK0,sK1),sK0)),
% 0.23/0.43    inference(unit_resulting_resolution,[],[f20,f13,f14,f17])).
% 0.23/0.43  fof(f17,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (r1_tarski(sK2(X0,X1,X2),X1) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f12])).
% 0.23/0.43  fof(f14,plain,(
% 0.23/0.43    sK0 != k3_xboole_0(sK0,sK1)),
% 0.23/0.43    inference(cnf_transformation,[],[f10])).
% 0.23/0.43  fof(f10,plain,(
% 0.23/0.43    sK0 != k3_xboole_0(sK0,sK1) & r1_tarski(sK0,sK1)),
% 0.23/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.23/0.43  fof(f9,plain,(
% 0.23/0.43    ? [X0,X1] : (k3_xboole_0(X0,X1) != X0 & r1_tarski(X0,X1)) => (sK0 != k3_xboole_0(sK0,sK1) & r1_tarski(sK0,sK1))),
% 0.23/0.43    introduced(choice_axiom,[])).
% 0.23/0.43  fof(f6,plain,(
% 0.23/0.43    ? [X0,X1] : (k3_xboole_0(X0,X1) != X0 & r1_tarski(X0,X1))),
% 0.23/0.43    inference(ennf_transformation,[],[f5])).
% 0.23/0.43  fof(f5,negated_conjecture,(
% 0.23/0.43    ~! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.43    inference(negated_conjecture,[],[f4])).
% 0.23/0.43  fof(f4,conjecture,(
% 0.23/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.43  fof(f13,plain,(
% 0.23/0.43    r1_tarski(sK0,sK1)),
% 0.23/0.43    inference(cnf_transformation,[],[f10])).
% 0.23/0.43  fof(f20,plain,(
% 0.23/0.43    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.23/0.43    inference(superposition,[],[f16,f15])).
% 0.23/0.43  fof(f15,plain,(
% 0.23/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.43    inference(cnf_transformation,[],[f1])).
% 0.23/0.43  fof(f1,axiom,(
% 0.23/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.43  fof(f16,plain,(
% 0.23/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f3])).
% 0.23/0.43  fof(f3,axiom,(
% 0.23/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.43  % SZS output end Proof for theBenchmark
% 0.23/0.43  % (27822)------------------------------
% 0.23/0.43  % (27822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.43  % (27822)Termination reason: Refutation
% 0.23/0.43  
% 0.23/0.43  % (27822)Memory used [KB]: 6012
% 0.23/0.43  % (27822)Time elapsed: 0.003 s
% 0.23/0.43  % (27822)------------------------------
% 0.23/0.43  % (27822)------------------------------
% 0.23/0.43  % (27819)Success in time 0.06 s
%------------------------------------------------------------------------------

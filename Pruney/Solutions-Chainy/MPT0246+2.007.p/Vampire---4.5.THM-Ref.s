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
% DateTime   : Thu Dec  3 12:37:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 168 expanded)
%              Number of leaves         :   11 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  106 ( 341 expanded)
%              Number of equality atoms :   58 ( 201 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f135,f87])).

fof(f87,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f84,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f84,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f83,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK0)))
      | r2_hidden(sK1,sK0) ) ),
    inference(superposition,[],[f28,f81])).

fof(f81,plain,(
    ! [X0] : sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(subsumption_resolution,[],[f80,f19])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ) ),
    inference(resolution,[],[f46,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK1 = sK2(sK0,X0) ) ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f135,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f134,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f134,plain,(
    ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f45,plain,(
    sK0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f18,f44])).

fof(f18,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f133,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f131,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    r1_tarski(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f129,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f129,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | r1_tarski(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f29,f127])).

fof(f127,plain,(
    sK1 = sK2(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f125,f45])).

fof(f125,plain,
    ( sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK1 = sK2(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f102,f87])).

fof(f102,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,sK0)
      | sK0 = k3_enumset1(X7,X7,X7,X7,X7)
      | sK1 = sK2(sK0,k3_enumset1(X7,X7,X7,X7,X7)) ) ),
    inference(resolution,[],[f48,f73])).

fof(f73,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | sK0 = X1
      | sK1 = sK2(sK0,X1) ) ),
    inference(resolution,[],[f26,f69])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (15676)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (15679)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (15684)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (15703)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (15693)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (15695)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.57  % (15679)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f135,f87])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    r2_hidden(sK1,sK0)),
% 0.22/0.57    inference(subsumption_resolution,[],[f84,f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    k1_xboole_0 != sK0),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.57    inference(negated_conjecture,[],[f11])).
% 0.22/0.57  fof(f11,conjecture,(
% 0.22/0.57    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 0.22/0.57    inference(resolution,[],[f83,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK0))) | r2_hidden(sK1,sK0)) )),
% 0.22/0.57    inference(superposition,[],[f28,f81])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    ( ! [X0] : (sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f80,f19])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = sK0 | sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) )),
% 0.22/0.57    inference(resolution,[],[f46,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(sK0,X0) | sK1 = sK2(sK0,X0)) )),
% 0.22/0.57    inference(resolution,[],[f28,f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    ~r2_hidden(sK1,sK0)),
% 0.22/0.57    inference(resolution,[],[f134,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f30,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f20,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f21,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f32,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.22/0.57    inference(subsumption_resolution,[],[f133,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    sK0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.57    inference(definition_unfolding,[],[f18,f44])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    sK0 != k1_tarski(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.57    inference(resolution,[],[f131,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f131,plain,(
% 0.22/0.57    r1_tarski(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.57    inference(subsumption_resolution,[],[f129,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 0.22/0.57    inference(equality_resolution,[],[f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 0.22/0.57    inference(equality_resolution,[],[f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.57    inference(definition_unfolding,[],[f41,f42])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.57  fof(f129,plain,(
% 0.22/0.57    ~r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | r1_tarski(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.57    inference(superposition,[],[f29,f127])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    sK1 = sK2(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.57    inference(subsumption_resolution,[],[f125,f45])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK1 = sK2(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.57    inference(resolution,[],[f102,f87])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    ( ! [X7] : (~r2_hidden(X7,sK0) | sK0 = k3_enumset1(X7,X7,X7,X7,X7) | sK1 = sK2(sK0,k3_enumset1(X7,X7,X7,X7,X7))) )),
% 0.22/0.57    inference(resolution,[],[f48,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X1] : (~r1_tarski(X1,sK0) | sK0 = X1 | sK1 = sK2(sK0,X1)) )),
% 0.22/0.57    inference(resolution,[],[f26,f69])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (15679)------------------------------
% 0.22/0.57  % (15679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (15679)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (15679)Memory used [KB]: 6268
% 0.22/0.57  % (15679)Time elapsed: 0.149 s
% 0.22/0.57  % (15679)------------------------------
% 0.22/0.57  % (15679)------------------------------
% 0.22/0.57  % (15682)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (15672)Success in time 0.214 s
%------------------------------------------------------------------------------

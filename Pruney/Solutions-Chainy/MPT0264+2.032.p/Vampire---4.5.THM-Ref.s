%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:25 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  75 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 124 expanded)
%              Number of equality atoms :   44 (  89 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f170,f15])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f170,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f155,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f17,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f18,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f155,plain,(
    r2_hidden(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f135,f14])).

fof(f14,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f135,plain,
    ( r2_hidden(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X0,X3] : r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f92,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
      | r2_hidden(X5,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X5,sK2) ) ),
    inference(superposition,[],[f60,f45])).

fof(f45,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f13,f44,f43])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f42])).

fof(f16,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f13,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (8373)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (8380)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.20/0.51  % (8383)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.51  % (8371)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.20/0.51  % (8376)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.20/0.52  % (8388)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.20/0.52  % (8386)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.20/0.52  % (8388)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % (8384)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.20/0.52  % (8393)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f171,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f170,f15])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    sK0 != sK1),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f11,plain,(
% 1.20/0.52    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.20/0.52    inference(ennf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.20/0.52    inference(negated_conjecture,[],[f9])).
% 1.20/0.52  fof(f9,conjecture,(
% 1.20/0.52    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 1.20/0.52  fof(f170,plain,(
% 1.20/0.52    sK0 = sK1),
% 1.20/0.52    inference(duplicate_literal_removal,[],[f158])).
% 1.20/0.52  fof(f158,plain,(
% 1.20/0.52    sK0 = sK1 | sK0 = sK1),
% 1.20/0.52    inference(resolution,[],[f155,f67])).
% 1.20/0.52  fof(f67,plain,(
% 1.20/0.52    ( ! [X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.20/0.52    inference(equality_resolution,[],[f48])).
% 1.20/0.52  fof(f48,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 1.20/0.52    inference(definition_unfolding,[],[f28,f43])).
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f17,f42])).
% 1.20/0.52  fof(f42,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f18,f41])).
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f31,f40])).
% 1.20/0.52  fof(f40,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.20/0.52    inference(cnf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.20/0.52  fof(f155,plain,(
% 1.20/0.52    r2_hidden(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.20/0.52    inference(subsumption_resolution,[],[f135,f14])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    r2_hidden(sK1,sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f135,plain,(
% 1.20/0.52    r2_hidden(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,sK2)),
% 1.20/0.52    inference(resolution,[],[f92,f64])).
% 1.20/0.52  fof(f64,plain,(
% 1.20/0.52    ( ! [X0,X3] : (r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X3))) )),
% 1.20/0.52    inference(equality_resolution,[],[f63])).
% 1.20/0.52  fof(f63,plain,(
% 1.20/0.52    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k4_enumset1(X0,X0,X0,X0,X0,X3) != X2) )),
% 1.20/0.52    inference(equality_resolution,[],[f46])).
% 1.20/0.52  fof(f46,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 1.20/0.52    inference(definition_unfolding,[],[f30,f43])).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.20/0.52    inference(cnf_transformation,[],[f3])).
% 1.20/0.52  fof(f92,plain,(
% 1.20/0.52    ( ! [X5] : (~r2_hidden(X5,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X5,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X5,sK2)) )),
% 1.20/0.52    inference(superposition,[],[f60,f45])).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 1.20/0.52    inference(definition_unfolding,[],[f13,f44,f43])).
% 1.20/0.52  fof(f44,plain,(
% 1.20/0.52    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f16,f42])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,axiom,(
% 1.20/0.52    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f60,plain,(
% 1.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(equality_resolution,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.20/0.52    inference(cnf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (8388)------------------------------
% 1.20/0.52  % (8388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (8388)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (8388)Memory used [KB]: 1791
% 1.20/0.52  % (8388)Time elapsed: 0.111 s
% 1.20/0.52  % (8388)------------------------------
% 1.20/0.52  % (8388)------------------------------
% 1.20/0.53  % (8370)Success in time 0.167 s
%------------------------------------------------------------------------------

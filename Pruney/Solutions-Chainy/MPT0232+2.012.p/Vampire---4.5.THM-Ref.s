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
% DateTime   : Thu Dec  3 12:37:01 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 160 expanded)
%              Number of leaves         :   11 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 244 expanded)
%              Number of equality atoms :   39 ( 167 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(subsumption_resolution,[],[f166,f150])).

fof(f150,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f96,f113])).

fof(f113,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f47,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f22,f45,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f47,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f15,f44,f45])).

fof(f15,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f46,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f16,f44,f45])).

fof(f16,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f66,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | ~ sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f66,plain,(
    ! [X4,X0,X1] : sP4(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP4(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f166,plain,(
    ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f154,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f26,f51,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f25,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f154,plain,(
    ! [X0] : ~ r2_hidden(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f153,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f153,plain,(
    ! [X0] : ~ sP6(sK1,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f150,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (14803)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (14832)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (14802)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (14823)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (14821)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.20/0.52  % (14814)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.20/0.52  % (14821)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f167,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f166,f150])).
% 1.20/0.52  fof(f150,plain,(
% 1.20/0.52    r2_hidden(sK1,k1_xboole_0)),
% 1.20/0.52    inference(superposition,[],[f96,f113])).
% 1.20/0.52  fof(f113,plain,(
% 1.20/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f46,f47,f50])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.20/0.52    inference(definition_unfolding,[],[f22,f45,f45])).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f21,f44])).
% 1.20/0.52  fof(f44,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f20,f35])).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f9])).
% 1.20/0.52  fof(f9,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,axiom,(
% 1.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.20/0.52  fof(f47,plain,(
% 1.20/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.20/0.52    inference(definition_unfolding,[],[f15,f44,f45])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.20/0.52    inference(ennf_transformation,[],[f12])).
% 1.20/0.52  fof(f12,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.20/0.52    inference(negated_conjecture,[],[f11])).
% 1.20/0.52  fof(f11,conjecture,(
% 1.20/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 1.20/0.52  fof(f46,plain,(
% 1.20/0.52    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.20/0.52    inference(definition_unfolding,[],[f16,f44,f45])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f96,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))) )),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f66,f65])).
% 1.20/0.52  fof(f65,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | ~sP4(X4,X2,X1,X0)) )),
% 1.20/0.52    inference(equality_resolution,[],[f55])).
% 1.20/0.52  fof(f55,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.20/0.52    inference(definition_unfolding,[],[f31,f35])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.20/0.52    inference(cnf_transformation,[],[f14])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.20/0.52    inference(ennf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.20/0.52  fof(f66,plain,(
% 1.20/0.52    ( ! [X4,X0,X1] : (sP4(X4,X4,X1,X0)) )),
% 1.20/0.52    inference(equality_resolution,[],[f29])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP4(X4,X2,X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f14])).
% 1.20/0.52  fof(f166,plain,(
% 1.20/0.52    ~r2_hidden(sK1,k1_xboole_0)),
% 1.20/0.52    inference(superposition,[],[f154,f79])).
% 1.20/0.52  fof(f79,plain,(
% 1.20/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f26,f51,f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.20/0.52  fof(f51,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f25,f43])).
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.20/0.52  fof(f154,plain,(
% 1.20/0.52    ( ! [X0] : (~r2_hidden(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) )),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f153,f69])).
% 1.20/0.52  fof(f69,plain,(
% 1.20/0.52    ( ! [X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.20/0.52    inference(equality_resolution,[],[f58])).
% 1.20/0.52  fof(f58,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.20/0.52    inference(definition_unfolding,[],[f40,f43])).
% 1.20/0.52  fof(f40,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.20/0.52    inference(cnf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.20/0.52  fof(f153,plain,(
% 1.20/0.52    ( ! [X0] : (~sP6(sK1,k1_xboole_0,X0)) )),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f150,f38])).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f1])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (14821)------------------------------
% 1.20/0.52  % (14821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (14821)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (14821)Memory used [KB]: 1791
% 1.20/0.52  % (14821)Time elapsed: 0.112 s
% 1.20/0.52  % (14821)------------------------------
% 1.20/0.52  % (14821)------------------------------
% 1.20/0.52  % (14832)Refutation not found, incomplete strategy% (14832)------------------------------
% 1.20/0.52  % (14832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (14832)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (14832)Memory used [KB]: 1663
% 1.20/0.52  % (14832)Time elapsed: 0.112 s
% 1.20/0.52  % (14832)------------------------------
% 1.20/0.52  % (14832)------------------------------
% 1.20/0.52  % (14796)Success in time 0.161 s
%------------------------------------------------------------------------------

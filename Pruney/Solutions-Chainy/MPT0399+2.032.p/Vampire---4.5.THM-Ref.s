%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 154 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :   79 ( 282 expanded)
%              Number of equality atoms :   41 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f78,plain,(
    k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f67,f77])).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_xboole_0(X0,X1) ),
    inference(forward_demodulation,[],[f76,f43])).

fof(f43,plain,(
    k1_xboole_0 = k3_tarski(sK0) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f42,plain,(
    r1_tarski(k3_tarski(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f41,f20])).

fof(f20,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f41,plain,(
    r1_tarski(k3_tarski(sK0),k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f26,f18])).

fof(f18,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(sK0) ),
    inference(backward_demodulation,[],[f75,f67])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f66,f63])).

fof(f63,plain,(
    ! [X1] : k1_tarski(X1) = sK0 ),
    inference(subsumption_resolution,[],[f62,f19])).

fof(f62,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK0
      | k1_tarski(X1) = sK0 ) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f60,plain,(
    ! [X4] : ~ r2_hidden(X4,sK0) ),
    inference(subsumption_resolution,[],[f58,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f58,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(k1_tarski(X3),k1_tarski(sK2(k1_xboole_0,X4))) != k4_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(sK2(k1_xboole_0,X4))),k1_xboole_0)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(resolution,[],[f39,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f28,f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X1,X2),X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) ) ),
    inference(definition_unfolding,[],[f34,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(sK0,k1_tarski(X1))) ),
    inference(backward_demodulation,[],[f36,f63])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f24,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f67,plain,(
    sK0 = k2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f37,f63])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21931)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (21923)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (21931)Refutation not found, incomplete strategy% (21931)------------------------------
% 0.22/0.51  % (21931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21914)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (21931)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  % (21915)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  
% 0.22/0.51  % (21931)Memory used [KB]: 10618
% 0.22/0.51  % (21931)Time elapsed: 0.057 s
% 0.22/0.51  % (21931)------------------------------
% 0.22/0.51  % (21931)------------------------------
% 0.22/0.51  % (21915)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (21909)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.51    inference(negated_conjecture,[],[f11])).
% 0.22/0.51  fof(f11,conjecture,(
% 0.22/0.51    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    k1_xboole_0 = sK0),
% 0.22/0.51    inference(backward_demodulation,[],[f67,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f76,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    k1_xboole_0 = k3_tarski(sK0)),
% 0.22/0.51    inference(resolution,[],[f42,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    r1_tarski(k3_tarski(sK0),k1_xboole_0)),
% 0.22/0.51    inference(forward_demodulation,[],[f41,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    r1_tarski(k3_tarski(sK0),k3_tarski(k1_xboole_0))),
% 0.22/0.51    inference(resolution,[],[f26,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    r1_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(sK0)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f75,f67])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(sK0,sK0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f66,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X1] : (k1_tarski(X1) = sK0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f62,f19])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = sK0 | k1_tarski(X1) = sK0) )),
% 0.22/0.51    inference(resolution,[],[f60,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f58,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(sK2(k1_xboole_0,X4))) != k4_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(sK2(k1_xboole_0,X4))),k1_xboole_0) | ~r2_hidden(X4,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f39,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f28,f18])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | r2_hidden(sK2(X1,X2),X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f34,f25,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(sK0,k1_tarski(X1)))) )),
% 0.22/0.51    inference(backward_demodulation,[],[f36,f63])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f24,f25])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    sK0 = k2_xboole_0(sK0,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f37,f63])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f22,f25])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (21915)------------------------------
% 0.22/0.51  % (21915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21915)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (21915)Memory used [KB]: 6268
% 0.22/0.51  % (21915)Time elapsed: 0.064 s
% 0.22/0.51  % (21915)------------------------------
% 0.22/0.51  % (21915)------------------------------
% 0.22/0.52  % (21907)Success in time 0.153 s
%------------------------------------------------------------------------------

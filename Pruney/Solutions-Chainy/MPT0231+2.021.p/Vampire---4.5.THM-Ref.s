%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:57 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 138 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 198 expanded)
%              Number of equality atoms :   69 ( 145 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(subsumption_resolution,[],[f189,f23])).

fof(f23,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f189,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f186,f136])).

fof(f136,plain,(
    r2_hidden(sK0,k2_tarski(sK2,sK2)) ),
    inference(forward_demodulation,[],[f134,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f134,plain,(
    r2_hidden(sK0,k5_xboole_0(k2_tarski(sK2,sK2),k1_xboole_0)) ),
    inference(superposition,[],[f90,f104])).

fof(f104,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f90,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X4,X2),k2_tarski(X0,X0)))) ),
    inference(backward_demodulation,[],[f63,f87])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f86,f25])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f85,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f50,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f51,f82])).

fof(f82,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X4,X3)) = X3 ),
    inference(resolution,[],[f35,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f30,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f63,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2))))) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2)))) != X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))) != X3 ) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))) ),
    inference(definition_unfolding,[],[f37,f46,f27])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f186,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X1,X1))
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f184,f25])).

fof(f184,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k2_tarski(X1,X1),k1_xboole_0))
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k2_tarski(X1,X1),k1_xboole_0))
      | X1 = X2
      | X1 = X2
      | X1 = X2 ) ),
    inference(superposition,[],[f92,f67])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))
      | X0 = X4
      | X1 = X4
      | X2 = X4 ) ),
    inference(backward_demodulation,[],[f66,f87])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2))))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))) != X3 ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:09:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (18283)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (18281)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (18300)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.53  % (18291)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (18281)Refutation not found, incomplete strategy% (18281)------------------------------
% 1.27/0.53  % (18281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (18281)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (18281)Memory used [KB]: 6268
% 1.27/0.53  % (18281)Time elapsed: 0.088 s
% 1.27/0.53  % (18281)------------------------------
% 1.27/0.53  % (18281)------------------------------
% 1.27/0.54  % (18283)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f199,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(subsumption_resolution,[],[f189,f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    sK0 != sK2),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.27/0.54    inference(ennf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.27/0.54    inference(negated_conjecture,[],[f15])).
% 1.27/0.54  fof(f15,conjecture,(
% 1.27/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 1.27/0.54  fof(f189,plain,(
% 1.27/0.54    sK0 = sK2),
% 1.27/0.54    inference(resolution,[],[f186,f136])).
% 1.27/0.54  fof(f136,plain,(
% 1.27/0.54    r2_hidden(sK0,k2_tarski(sK2,sK2))),
% 1.27/0.54    inference(forward_demodulation,[],[f134,f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.27/0.54  fof(f134,plain,(
% 1.27/0.54    r2_hidden(sK0,k5_xboole_0(k2_tarski(sK2,sK2),k1_xboole_0))),
% 1.27/0.54    inference(superposition,[],[f90,f104])).
% 1.27/0.54  fof(f104,plain,(
% 1.27/0.54    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),
% 1.27/0.54    inference(resolution,[],[f36,f49])).
% 1.27/0.54  fof(f49,plain,(
% 1.27/0.54    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),
% 1.27/0.54    inference(definition_unfolding,[],[f22,f27])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,axiom,(
% 1.27/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 1.27/0.54    inference(unused_predicate_definition_removal,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.27/0.54  fof(f90,plain,(
% 1.27/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X4,X2),k2_tarski(X0,X0))))) )),
% 1.27/0.54    inference(backward_demodulation,[],[f63,f87])).
% 1.27/0.54  fof(f87,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.27/0.54    inference(forward_demodulation,[],[f86,f25])).
% 1.27/0.54  fof(f86,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) )),
% 1.27/0.54    inference(forward_demodulation,[],[f85,f67])).
% 1.27/0.54  fof(f67,plain,(
% 1.27/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.27/0.54    inference(backward_demodulation,[],[f50,f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.27/0.54  fof(f50,plain,(
% 1.27/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f24,f31])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.27/0.54  fof(f85,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0))) )),
% 1.27/0.54    inference(backward_demodulation,[],[f51,f82])).
% 1.27/0.54  fof(f82,plain,(
% 1.27/0.54    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,X3)) = X3) )),
% 1.27/0.54    inference(resolution,[],[f35,f73])).
% 1.27/0.54  fof(f73,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.27/0.54    inference(resolution,[],[f33,f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.27/0.54  fof(f51,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f30,f46,f46])).
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f32,f31])).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.27/0.54  fof(f63,plain,(
% 1.27/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2)))))) )),
% 1.27/0.54    inference(equality_resolution,[],[f62])).
% 1.27/0.54  fof(f62,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X4,X2)))) != X3) )),
% 1.27/0.54    inference(equality_resolution,[],[f53])).
% 1.27/0.54  fof(f53,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))) != X3) )),
% 1.27/0.54    inference(definition_unfolding,[],[f44,f47])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2))))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f37,f46,f27])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f12])).
% 1.27/0.54  fof(f12,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.27/0.54    inference(cnf_transformation,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.27/0.54    inference(ennf_transformation,[],[f11])).
% 1.27/0.54  fof(f11,axiom,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.27/0.54  fof(f186,plain,(
% 1.27/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k2_tarski(X1,X1)) | X1 = X2) )),
% 1.27/0.54    inference(forward_demodulation,[],[f184,f25])).
% 1.27/0.54  fof(f184,plain,(
% 1.27/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(k2_tarski(X1,X1),k1_xboole_0)) | X1 = X2) )),
% 1.27/0.54    inference(duplicate_literal_removal,[],[f183])).
% 1.27/0.54  fof(f183,plain,(
% 1.27/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(k2_tarski(X1,X1),k1_xboole_0)) | X1 = X2 | X1 = X2 | X1 = X2) )),
% 1.27/0.54    inference(superposition,[],[f92,f67])).
% 1.27/0.54  fof(f92,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) | X0 = X4 | X1 = X4 | X2 = X4) )),
% 1.27/0.54    inference(backward_demodulation,[],[f66,f87])).
% 1.27/0.54  fof(f66,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))))) )),
% 1.27/0.54    inference(equality_resolution,[],[f55])).
% 1.27/0.54  fof(f55,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))) != X3) )),
% 1.27/0.54    inference(definition_unfolding,[],[f42,f47])).
% 1.27/0.54  fof(f42,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.27/0.54    inference(cnf_transformation,[],[f21])).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (18283)------------------------------
% 1.27/0.54  % (18283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (18283)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (18283)Memory used [KB]: 6268
% 1.27/0.54  % (18283)Time elapsed: 0.115 s
% 1.27/0.54  % (18283)------------------------------
% 1.27/0.54  % (18283)------------------------------
% 1.27/0.54  % (18276)Success in time 0.174 s
%------------------------------------------------------------------------------

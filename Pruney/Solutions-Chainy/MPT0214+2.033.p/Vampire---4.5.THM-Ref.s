%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:02 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 (  92 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 121 expanded)
%              Number of equality atoms :   54 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f104,plain,(
    ~ r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) ),
    inference(backward_demodulation,[],[f95,f100])).

fof(f100,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK0) ),
    inference(superposition,[],[f99,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f99,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f98,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f98,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f51,f96])).

fof(f96,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f52,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f52,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f21,f50,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f24,f47,f32,f50])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f95,plain,(
    ~ r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f26,f50])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.08/0.26  % Computer   : n024.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 17:34:21 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.13/0.36  % (15668)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.13/0.39  % (15685)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.13/0.40  % (15693)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.13/0.42  % (15673)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.13/0.42  % (15690)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.13/0.43  % (15682)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.13/0.43  % (15666)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.13/0.43  % (15690)Refutation found. Thanks to Tanya!
% 0.13/0.43  % SZS status Theorem for theBenchmark
% 0.13/0.43  % SZS output start Proof for theBenchmark
% 0.13/0.43  fof(f107,plain,(
% 0.13/0.43    $false),
% 0.13/0.43    inference(resolution,[],[f104,f70])).
% 0.13/0.43  fof(f70,plain,(
% 0.13/0.43    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 0.13/0.43    inference(equality_resolution,[],[f69])).
% 0.13/0.43  fof(f69,plain,(
% 0.13/0.43    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 0.13/0.43    inference(equality_resolution,[],[f58])).
% 0.13/0.43  fof(f58,plain,(
% 0.13/0.43    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.13/0.43    inference(definition_unfolding,[],[f42,f48])).
% 0.13/0.43  fof(f48,plain,(
% 0.13/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.13/0.43    inference(definition_unfolding,[],[f33,f32])).
% 0.13/0.43  fof(f32,plain,(
% 0.13/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.13/0.43    inference(cnf_transformation,[],[f12])).
% 0.13/0.43  fof(f12,axiom,(
% 0.13/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.13/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.13/0.44  fof(f33,plain,(
% 0.13/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.13/0.44    inference(cnf_transformation,[],[f11])).
% 0.13/0.44  fof(f11,axiom,(
% 0.13/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.13/0.44  fof(f42,plain,(
% 0.13/0.44    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.13/0.44    inference(cnf_transformation,[],[f20])).
% 0.13/0.44  fof(f20,plain,(
% 0.13/0.44    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.13/0.44    inference(ennf_transformation,[],[f6])).
% 0.13/0.44  fof(f6,axiom,(
% 0.13/0.44    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.13/0.44  fof(f104,plain,(
% 0.13/0.44    ~r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK0))),
% 0.13/0.44    inference(backward_demodulation,[],[f95,f100])).
% 0.13/0.44  fof(f100,plain,(
% 0.13/0.44    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK0)),
% 0.13/0.44    inference(superposition,[],[f99,f44])).
% 0.13/0.44  fof(f44,plain,(
% 0.13/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.13/0.44    inference(cnf_transformation,[],[f3])).
% 0.13/0.44  fof(f3,axiom,(
% 0.13/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.13/0.44  fof(f99,plain,(
% 0.13/0.44    k3_enumset1(sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 0.13/0.44    inference(forward_demodulation,[],[f98,f45])).
% 0.13/0.44  fof(f45,plain,(
% 0.13/0.44    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.13/0.44    inference(cnf_transformation,[],[f4])).
% 0.13/0.44  fof(f4,axiom,(
% 0.13/0.44    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.13/0.44  fof(f98,plain,(
% 0.13/0.44    k3_enumset1(sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.13/0.44    inference(superposition,[],[f51,f96])).
% 0.13/0.44  fof(f96,plain,(
% 0.13/0.44    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.13/0.44    inference(unit_resulting_resolution,[],[f52,f23])).
% 0.13/0.44  fof(f23,plain,(
% 0.13/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.13/0.44    inference(cnf_transformation,[],[f19])).
% 0.13/0.44  fof(f19,plain,(
% 0.13/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.13/0.44    inference(ennf_transformation,[],[f2])).
% 0.13/0.44  fof(f2,axiom,(
% 0.13/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.13/0.44  fof(f52,plain,(
% 0.13/0.44    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.13/0.44    inference(definition_unfolding,[],[f21,f50,f50])).
% 0.13/0.44  fof(f50,plain,(
% 0.13/0.44    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.13/0.44    inference(definition_unfolding,[],[f29,f49])).
% 0.13/0.44  fof(f49,plain,(
% 0.13/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.13/0.44    inference(definition_unfolding,[],[f43,f48])).
% 0.13/0.44  fof(f43,plain,(
% 0.13/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.13/0.44    inference(cnf_transformation,[],[f10])).
% 0.13/0.44  fof(f10,axiom,(
% 0.13/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.13/0.44  fof(f29,plain,(
% 0.13/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.13/0.44    inference(cnf_transformation,[],[f9])).
% 0.13/0.44  fof(f9,axiom,(
% 0.13/0.44    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.13/0.44  fof(f21,plain,(
% 0.13/0.44    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.13/0.44    inference(cnf_transformation,[],[f18])).
% 0.13/0.44  fof(f18,plain,(
% 0.13/0.44    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.13/0.44    inference(ennf_transformation,[],[f17])).
% 0.13/0.44  fof(f17,negated_conjecture,(
% 0.13/0.44    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.13/0.44    inference(negated_conjecture,[],[f16])).
% 0.13/0.44  fof(f16,conjecture,(
% 0.13/0.44    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.13/0.44  fof(f51,plain,(
% 0.13/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3))))) )),
% 0.13/0.44    inference(definition_unfolding,[],[f24,f47,f32,f50])).
% 0.13/0.44  fof(f47,plain,(
% 0.13/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.13/0.44    inference(definition_unfolding,[],[f31,f30])).
% 0.13/0.44  fof(f30,plain,(
% 0.13/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.13/0.44    inference(cnf_transformation,[],[f1])).
% 0.13/0.44  fof(f1,axiom,(
% 0.13/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.13/0.44  fof(f31,plain,(
% 0.13/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.13/0.44    inference(cnf_transformation,[],[f5])).
% 0.13/0.44  fof(f5,axiom,(
% 0.13/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.13/0.44  fof(f24,plain,(
% 0.13/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.13/0.44    inference(cnf_transformation,[],[f8])).
% 0.13/0.44  fof(f8,axiom,(
% 0.13/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.13/0.44  fof(f95,plain,(
% 0.13/0.44    ~r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.13/0.44    inference(unit_resulting_resolution,[],[f22,f66])).
% 0.13/0.44  fof(f66,plain,(
% 0.13/0.44    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 0.13/0.44    inference(equality_resolution,[],[f55])).
% 0.13/0.44  fof(f55,plain,(
% 0.13/0.44    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 0.13/0.44    inference(definition_unfolding,[],[f26,f50])).
% 0.13/0.44  fof(f26,plain,(
% 0.13/0.44    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.13/0.44    inference(cnf_transformation,[],[f7])).
% 0.13/0.44  fof(f7,axiom,(
% 0.13/0.44    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.13/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.13/0.44  fof(f22,plain,(
% 0.13/0.44    sK0 != sK1),
% 0.13/0.44    inference(cnf_transformation,[],[f18])).
% 0.13/0.44  % SZS output end Proof for theBenchmark
% 0.13/0.44  % (15690)------------------------------
% 0.13/0.44  % (15690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.44  % (15690)Termination reason: Refutation
% 0.13/0.44  
% 0.13/0.44  % (15690)Memory used [KB]: 6268
% 0.13/0.44  % (15690)Time elapsed: 0.100 s
% 0.13/0.44  % (15690)------------------------------
% 0.13/0.44  % (15690)------------------------------
% 0.13/0.44  % (15664)Success in time 0.158 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:49:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 245 expanded)
%              Number of leaves         :   10 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 423 expanded)
%              Number of equality atoms :   33 ( 186 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f149])).

fof(f149,plain,(
    ! [X0] : r2_hidden(sK2(k8_relat_1(k1_xboole_0,sK0)),X0) ),
    inference(resolution,[],[f108,f114])).

fof(f114,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k8_relat_1(k1_xboole_0,sK0))
      | r2_hidden(X8,X6) ) ),
    inference(subsumption_resolution,[],[f112,f100])).

fof(f100,plain,(
    v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f91,f86])).

fof(f86,plain,(
    ! [X0] : k8_relat_1(k1_xboole_0,sK0) = k8_relat_1(k1_xboole_0,k8_relat_1(X0,sK0)) ),
    inference(forward_demodulation,[],[f79,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f79,plain,(
    ! [X0] : k8_relat_1(k1_xboole_0,k8_relat_1(X0,sK0)) = k8_relat_1(k4_xboole_0(k1_xboole_0,k1_xboole_0),sK0) ),
    inference(superposition,[],[f67,f21])).

fof(f67,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK0) ),
    inference(resolution,[],[f40,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f91,plain,(
    ! [X8,X9] : v1_relat_1(k8_relat_1(X8,k8_relat_1(X9,sK0))) ),
    inference(subsumption_resolution,[],[f85,f18])).

fof(f85,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k8_relat_1(X8,k8_relat_1(X9,sK0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f25,f67])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f112,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k8_relat_1(k1_xboole_0,sK0))
      | r2_hidden(X8,X6)
      | ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) ) ),
    inference(superposition,[],[f50,f87])).

fof(f87,plain,(
    ! [X1] : k8_relat_1(k1_xboole_0,sK0) = k8_relat_1(X1,k8_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f80,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f39,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f80,plain,(
    ! [X1] : k8_relat_1(X1,k8_relat_1(k1_xboole_0,sK0)) = k8_relat_1(k4_xboole_0(X1,X1),sK0) ),
    inference(superposition,[],[f67,f22])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f43,f25])).

fof(f43,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f108,plain,(
    r2_hidden(k4_tarski(sK1(k8_relat_1(k1_xboole_0,sK0)),sK2(k8_relat_1(k1_xboole_0,sK0))),k8_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f105,f19])).

fof(f19,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f105,plain,
    ( r2_hidden(k4_tarski(sK1(k8_relat_1(k1_xboole_0,sK0)),sK2(k8_relat_1(k1_xboole_0,sK0))),k8_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f100,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f157,plain,(
    ! [X2,X3] : ~ r2_hidden(sK2(k8_relat_1(k1_xboole_0,sK0)),k4_xboole_0(X2,X3)) ),
    inference(resolution,[],[f149,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:35:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.50  % (18666)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (18647)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (18658)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (18648)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (18650)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (18649)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (18649)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f157,f149])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(k8_relat_1(k1_xboole_0,sK0)),X0)) )),
% 0.20/0.51    inference(resolution,[],[f108,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (~r2_hidden(k4_tarski(X7,X8),k8_relat_1(k1_xboole_0,sK0)) | r2_hidden(X8,X6)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f112,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    v1_relat_1(k8_relat_1(k1_xboole_0,sK0))),
% 0.20/0.51    inference(superposition,[],[f91,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X0] : (k8_relat_1(k1_xboole_0,sK0) = k8_relat_1(k1_xboole_0,k8_relat_1(X0,sK0))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f79,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (k8_relat_1(k1_xboole_0,k8_relat_1(X0,sK0)) = k8_relat_1(k4_xboole_0(k1_xboole_0,k1_xboole_0),sK0)) )),
% 0.20/0.51    inference(superposition,[],[f67,f21])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK0)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK0)) )),
% 0.20/0.51    inference(resolution,[],[f40,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f32,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X8,X9] : (v1_relat_1(k8_relat_1(X8,k8_relat_1(X9,sK0)))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f85,f18])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X8,X9] : (v1_relat_1(k8_relat_1(X8,k8_relat_1(X9,sK0))) | ~v1_relat_1(sK0)) )),
% 0.20/0.51    inference(superposition,[],[f25,f67])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (~r2_hidden(k4_tarski(X7,X8),k8_relat_1(k1_xboole_0,sK0)) | r2_hidden(X8,X6) | ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0))) )),
% 0.20/0.51    inference(superposition,[],[f50,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X1] : (k8_relat_1(k1_xboole_0,sK0) = k8_relat_1(X1,k8_relat_1(k1_xboole_0,sK0))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f80,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(backward_demodulation,[],[f39,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f20,f24])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X1] : (k8_relat_1(X1,k8_relat_1(k1_xboole_0,sK0)) = k8_relat_1(k4_xboole_0(X1,X1),sK0)) )),
% 0.20/0.51    inference(superposition,[],[f67,f22])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) | r2_hidden(X4,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f43,f25])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK1(k8_relat_1(k1_xboole_0,sK0)),sK2(k8_relat_1(k1_xboole_0,sK0))),k8_relat_1(k1_xboole_0,sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f105,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK1(k8_relat_1(k1_xboole_0,sK0)),sK2(k8_relat_1(k1_xboole_0,sK0))),k8_relat_1(k1_xboole_0,sK0)) | k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.20/0.51    inference(resolution,[],[f100,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r2_hidden(sK2(k8_relat_1(k1_xboole_0,sK0)),k4_xboole_0(X2,X3))) )),
% 0.20/0.51    inference(resolution,[],[f149,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (18649)------------------------------
% 0.20/0.52  % (18649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18649)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (18649)Memory used [KB]: 6396
% 0.20/0.52  % (18649)Time elapsed: 0.106 s
% 0.20/0.52  % (18649)------------------------------
% 0.20/0.52  % (18649)------------------------------
% 0.20/0.52  % (18644)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (18642)Success in time 0.176 s
%------------------------------------------------------------------------------

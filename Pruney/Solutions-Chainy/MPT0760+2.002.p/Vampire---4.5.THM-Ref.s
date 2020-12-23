%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  38 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 ( 102 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(subsumption_resolution,[],[f286,f15])).

fof(f15,plain,(
    k1_xboole_0 != k1_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

fof(f286,plain,(
    k1_xboole_0 = k1_wellord1(sK1,sK0) ),
    inference(resolution,[],[f276,f14])).

fof(f14,plain,(
    ~ r2_hidden(sK0,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f276,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(sK1))
      | k1_xboole_0 = k1_wellord1(sK1,X0) ) ),
    inference(resolution,[],[f270,f16])).

fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f270,plain,(
    ! [X8,X7] :
      ( ~ v1_xboole_0(X8)
      | r2_hidden(X7,k3_relat_1(sK1))
      | k1_wellord1(sK1,X7) = X8 ) ),
    inference(resolution,[],[f173,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f173,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(sK1,X2,X3),X3)
      | k1_wellord1(sK1,X2) = X3
      | r2_hidden(X2,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
      | r2_hidden(X9,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f13,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK2(sK1,X4,X5),X4),sK1)
      | r2_hidden(sK2(sK1,X4,X5),X5)
      | k1_wellord1(sK1,X4) = X5 ) ),
    inference(resolution,[],[f13,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k1_wellord1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:07:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (13352)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (13352)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f289,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f286,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    k1_xboole_0 != k1_wellord1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    k1_xboole_0 = k1_wellord1(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f276,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ~r2_hidden(sK0,k3_relat_1(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(X0,k3_relat_1(sK1)) | k1_xboole_0 = k1_wellord1(sK1,X0)) )),
% 0.22/0.48    inference(resolution,[],[f270,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f270,plain,(
% 0.22/0.48    ( ! [X8,X7] : (~v1_xboole_0(X8) | r2_hidden(X7,k3_relat_1(sK1)) | k1_wellord1(sK1,X7) = X8) )),
% 0.22/0.48    inference(resolution,[],[f173,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    ( ! [X2,X3] : (r2_hidden(sK2(sK1,X2,X3),X3) | k1_wellord1(sK1,X2) = X3 | r2_hidden(X2,k3_relat_1(sK1))) )),
% 0.22/0.48    inference(resolution,[],[f39,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),sK1) | r2_hidden(X9,k3_relat_1(sK1))) )),
% 0.22/0.48    inference(resolution,[],[f13,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X4,X5] : (r2_hidden(k4_tarski(sK2(sK1,X4,X5),X4),sK1) | r2_hidden(sK2(sK1,X4,X5),X5) | k1_wellord1(sK1,X4) = X5) )),
% 0.22/0.48    inference(resolution,[],[f13,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k1_wellord1(X0,X1) = X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (13352)------------------------------
% 0.22/0.48  % (13352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13352)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (13352)Memory used [KB]: 1791
% 0.22/0.48  % (13352)Time elapsed: 0.015 s
% 0.22/0.48  % (13352)------------------------------
% 0.22/0.48  % (13352)------------------------------
% 0.22/0.48  % (13353)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (13336)Success in time 0.115 s
%------------------------------------------------------------------------------

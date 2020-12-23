%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:22 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   31 (  42 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  65 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(subsumption_resolution,[],[f292,f310])).

fof(f310,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f212,f301])).

fof(f301,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(resolution,[],[f217,f83])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f217,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X2),X1) ) ),
    inference(forward_demodulation,[],[f216,f183])).

fof(f183,plain,(
    ! [X2,X1] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f86,f66])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f216,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f215,f66])).

fof(f215,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ) ),
    inference(superposition,[],[f90,f71])).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f212,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f210,f70])).

fof(f70,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f210,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2)) ),
    inference(resolution,[],[f87,f66])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f292,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f61,f183])).

fof(f61,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (3676)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.14/0.43  % (3676)Refutation found. Thanks to Tanya!
% 0.14/0.43  % SZS status Theorem for theBenchmark
% 0.14/0.43  % SZS output start Proof for theBenchmark
% 0.14/0.43  fof(f311,plain,(
% 0.14/0.43    $false),
% 0.14/0.43    inference(subsumption_resolution,[],[f292,f310])).
% 0.14/0.43  fof(f310,plain,(
% 0.14/0.43    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(k3_xboole_0(X1,X2))) )),
% 0.14/0.43    inference(backward_demodulation,[],[f212,f301])).
% 0.14/0.43  fof(f301,plain,(
% 0.14/0.43    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2)) = k6_relat_1(k3_xboole_0(X1,X2))) )),
% 0.14/0.43    inference(resolution,[],[f217,f83])).
% 0.14/0.43  fof(f83,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f6])).
% 0.14/0.43  fof(f6,axiom,(
% 0.14/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.14/0.43  fof(f217,plain,(
% 0.14/0.43    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X2),X1)) )),
% 0.14/0.43    inference(forward_demodulation,[],[f216,f183])).
% 0.14/0.43  fof(f183,plain,(
% 0.14/0.43    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.14/0.43    inference(resolution,[],[f86,f66])).
% 0.14/0.43  fof(f66,plain,(
% 0.14/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.43    inference(cnf_transformation,[],[f18])).
% 0.14/0.43  fof(f18,axiom,(
% 0.14/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.14/0.43  fof(f86,plain,(
% 0.14/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f49])).
% 0.14/0.43  fof(f49,plain,(
% 0.14/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.14/0.43    inference(ennf_transformation,[],[f34])).
% 0.14/0.43  fof(f34,axiom,(
% 0.14/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.14/0.43  fof(f216,plain,(
% 0.14/0.43    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) )),
% 0.14/0.43    inference(subsumption_resolution,[],[f215,f66])).
% 0.14/0.43  fof(f215,plain,(
% 0.14/0.43    ( ! [X2,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(k6_relat_1(X1)) | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) )),
% 0.14/0.43    inference(superposition,[],[f90,f71])).
% 0.14/0.43  fof(f71,plain,(
% 0.14/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.14/0.43    inference(cnf_transformation,[],[f28])).
% 0.14/0.43  fof(f28,axiom,(
% 0.14/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.14/0.43  fof(f90,plain,(
% 0.14/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.14/0.43    inference(cnf_transformation,[],[f53])).
% 0.14/0.43  fof(f53,plain,(
% 0.14/0.43    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.14/0.43    inference(flattening,[],[f52])).
% 0.14/0.43  fof(f52,plain,(
% 0.14/0.43    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.14/0.43    inference(ennf_transformation,[],[f31])).
% 0.14/0.43  fof(f31,axiom,(
% 0.14/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.14/0.43  fof(f212,plain,(
% 0.14/0.43    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2))) )),
% 0.14/0.43    inference(forward_demodulation,[],[f210,f70])).
% 0.14/0.43  fof(f70,plain,(
% 0.14/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.14/0.43    inference(cnf_transformation,[],[f28])).
% 0.14/0.43  fof(f210,plain,(
% 0.14/0.43    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2))) )),
% 0.14/0.43    inference(resolution,[],[f87,f66])).
% 0.14/0.43  fof(f87,plain,(
% 0.14/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.14/0.43    inference(cnf_transformation,[],[f50])).
% 0.14/0.43  fof(f50,plain,(
% 0.14/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.14/0.43    inference(ennf_transformation,[],[f23])).
% 0.14/0.43  fof(f23,axiom,(
% 0.14/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.14/0.43  fof(f292,plain,(
% 0.14/0.43    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.14/0.43    inference(superposition,[],[f61,f183])).
% 0.14/0.43  fof(f61,plain,(
% 0.14/0.43    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.14/0.43    inference(cnf_transformation,[],[f38])).
% 0.14/0.43  fof(f38,plain,(
% 0.14/0.43    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.14/0.43    inference(ennf_transformation,[],[f37])).
% 0.14/0.43  fof(f37,negated_conjecture,(
% 0.14/0.43    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.14/0.43    inference(negated_conjecture,[],[f36])).
% 0.14/0.43  fof(f36,conjecture,(
% 0.14/0.43    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.14/0.43  % SZS output end Proof for theBenchmark
% 0.14/0.43  % (3676)------------------------------
% 0.14/0.43  % (3676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.43  % (3676)Termination reason: Refutation
% 0.14/0.43  
% 0.14/0.43  % (3676)Memory used [KB]: 1791
% 0.14/0.43  % (3676)Time elapsed: 0.009 s
% 0.14/0.43  % (3676)------------------------------
% 0.14/0.43  % (3676)------------------------------
% 0.21/0.43  % (3658)Success in time 0.065 s
%------------------------------------------------------------------------------

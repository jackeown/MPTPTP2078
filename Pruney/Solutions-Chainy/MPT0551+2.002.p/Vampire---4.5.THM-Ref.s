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
% DateTime   : Thu Dec  3 12:49:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  63 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   52 ( 113 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,(
    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f15,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f48,f21])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f18,f14])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k2_relat_1(k7_relat_1(sK2,k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X1] : k7_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) ),
    inference(resolution,[],[f20,f14])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f45,f21])).

fof(f45,plain,(
    ! [X0,X1] : k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k9_relat_1(sK2,X1)) ),
    inference(resolution,[],[f44,f14])).

fof(f44,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(k7_relat_1(X1,X2),k7_relat_1(sK2,X3))) = k2_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),k9_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f40,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k2_xboole_0(X0,k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(X0),k9_relat_1(sK2,X1)) ) ),
    inference(forward_demodulation,[],[f38,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(k7_relat_1(sK2,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f25,f14])).

fof(f25,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k2_xboole_0(X1,k7_relat_1(X2,X3))) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(k7_relat_1(X2,X3)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f16,f17])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f15,plain,(
    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (12907)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (12913)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (12922)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (12904)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (12902)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (12907)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k9_relat_1(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.52    inference(superposition,[],[f15,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f48,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f18,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k2_relat_1(k7_relat_1(sK2,k2_xboole_0(X0,X1)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f47,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) )),
% 0.21/0.52    inference(resolution,[],[f20,f14])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f45,f21])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k9_relat_1(sK2,X1))) )),
% 0.21/0.52    inference(resolution,[],[f44,f14])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k2_relat_1(k2_xboole_0(k7_relat_1(X1,X2),k7_relat_1(sK2,X3))) = k2_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),k9_relat_1(sK2,X3))) )),
% 0.21/0.52    inference(resolution,[],[f40,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k2_xboole_0(X0,k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f38,f21])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,k7_relat_1(sK2,X1))) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(k7_relat_1(sK2,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f25,f14])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k2_relat_1(k2_xboole_0(X1,k7_relat_1(X2,X3))) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(k7_relat_1(X2,X3))) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(resolution,[],[f16,f17])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12907)------------------------------
% 0.21/0.52  % (12907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12907)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12907)Memory used [KB]: 6268
% 0.21/0.52  % (12907)Time elapsed: 0.113 s
% 0.21/0.52  % (12907)------------------------------
% 0.21/0.52  % (12907)------------------------------
% 0.21/0.52  % (12901)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (12900)Success in time 0.155 s
%------------------------------------------------------------------------------

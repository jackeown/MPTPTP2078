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
% DateTime   : Thu Dec  3 12:48:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  44 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f31,plain,(
    ! [X0] : ~ v1_relat_1(X0) ),
    inference(global_subsumption,[],[f15,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f29,f16])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k3_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f28,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f26,f17])).

fof(f17,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f25,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_relat_1(X2) = k2_xboole_0(k1_relat_1(X2),k2_relat_1(X2))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f15,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f9,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (13922)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (13923)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (13919)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (13921)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (13919)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(resolution,[],[f31,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0)) )),
% 0.21/0.43    inference(global_subsumption,[],[f15,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f29,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k3_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f28,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f26,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(resolution,[],[f25,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_relat_1(X2) = k2_xboole_0(k1_relat_1(X2),k2_relat_1(X2)) | ~v1_relat_1(X3)) )),
% 0.21/0.43    inference(resolution,[],[f20,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (13919)------------------------------
% 0.21/0.44  % (13919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (13919)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (13919)Memory used [KB]: 6012
% 0.21/0.44  % (13919)Time elapsed: 0.004 s
% 0.21/0.44  % (13919)------------------------------
% 0.21/0.44  % (13919)------------------------------
% 0.21/0.44  % (13913)Success in time 0.074 s
%------------------------------------------------------------------------------

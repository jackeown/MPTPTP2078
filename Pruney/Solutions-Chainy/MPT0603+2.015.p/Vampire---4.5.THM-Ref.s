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
% DateTime   : Thu Dec  3 12:51:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  85 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :   60 ( 179 expanded)
%              Number of equality atoms :   41 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f57,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f57,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f53,f24])).

fof(f53,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f50,f52])).

fof(f52,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f51,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    k7_relat_1(sK2,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f13,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f50,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0)),k7_relat_1(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f49,f30])).

fof(f30,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0)),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f41,f27])).

fof(f27,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f13,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f41,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0)),k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f15,f38,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    k1_xboole_0 != k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f37,f30])).

fof(f37,plain,(
    k1_xboole_0 != k2_zfmisc_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f35,f27])).

fof(f35,plain,(
    k1_xboole_0 != k2_zfmisc_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f15,f15,f18])).

fof(f15,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (11004)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (11009)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (11013)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (11009)Refutation not found, incomplete strategy% (11009)------------------------------
% 0.20/0.51  % (11009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11004)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0),
% 0.20/0.51    inference(superposition,[],[f57,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    inference(forward_demodulation,[],[f53,f24])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f50,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.20/0.51    inference(forward_demodulation,[],[f51,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    k7_relat_1(sK2,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0)),
% 0.20/0.51    inference(superposition,[],[f26,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f13,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0)),k7_relat_1(sK2,k1_xboole_0))),
% 0.20/0.51    inference(forward_demodulation,[],[f49,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f14,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    r1_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0)),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),
% 0.20/0.51    inference(forward_demodulation,[],[f41,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f13,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0)),k7_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f15,f38,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k7_relat_1(sK2,k1_xboole_0),k7_relat_1(sK2,k1_xboole_0))),
% 0.20/0.51    inference(forward_demodulation,[],[f37,f30])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))),
% 0.20/0.51    inference(forward_demodulation,[],[f35,f27])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f15,f15,f18])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (11004)------------------------------
% 0.20/0.51  % (11004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11004)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (11004)Memory used [KB]: 6140
% 0.20/0.51  % (11004)Time elapsed: 0.106 s
% 0.20/0.51  % (11004)------------------------------
% 0.20/0.51  % (11004)------------------------------
% 0.20/0.51  % (10999)Success in time 0.151 s
%------------------------------------------------------------------------------

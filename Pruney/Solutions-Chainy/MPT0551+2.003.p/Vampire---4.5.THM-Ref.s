%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  76 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 154 expanded)
%              Number of equality atoms :   26 (  70 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f44,f21])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

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
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k2_relat_1(k7_relat_1(sK2,k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f43,f29])).

fof(f29,plain,(
    ! [X0,X1] : k7_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) ),
    inference(resolution,[],[f17,f15])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(forward_demodulation,[],[f41,f21])).

fof(f41,plain,(
    ! [X0,X1] : k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k9_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X1))) ),
    inference(resolution,[],[f38,f15])).

fof(f38,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X1),k7_relat_1(X2,X3))) = k2_xboole_0(k9_relat_1(sK2,X1),k2_relat_1(k7_relat_1(X2,X3))) ) ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k2_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f34,f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),X1)) = k2_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f24,f15])).

fof(f24,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k2_xboole_0(k7_relat_1(X2,X3),X1)) = k2_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f19,f20])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f16,plain,(
    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.53  % (21820)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (21820)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (21827)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (21828)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f16,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k2_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f44,f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.20/0.55    inference(resolution,[],[f18,f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    v1_relat_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f8,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f6])).
% 0.20/0.55  fof(f6,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k2_relat_1(k7_relat_1(sK2,k2_xboole_0(X0,X1)))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f43,f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k7_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) )),
% 0.20/0.55    inference(resolution,[],[f17,f15])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f41,f21])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k2_xboole_0(k9_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X1)))) )),
% 0.20/0.55    inference(resolution,[],[f38,f15])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X1),k7_relat_1(X2,X3))) = k2_xboole_0(k9_relat_1(sK2,X1),k2_relat_1(k7_relat_1(X2,X3)))) )),
% 0.20/0.55    inference(resolution,[],[f36,f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k2_relat_1(X1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f34,f21])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(k7_relat_1(sK2,X0),X1)) = k2_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(resolution,[],[f24,f15])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k2_relat_1(k2_xboole_0(k7_relat_1(X2,X3),X1)) = k2_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(resolution,[],[f19,f20])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    k9_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (21820)------------------------------
% 0.20/0.56  % (21820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (21820)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (21820)Memory used [KB]: 6268
% 0.20/0.56  % (21820)Time elapsed: 0.130 s
% 0.20/0.56  % (21820)------------------------------
% 0.20/0.56  % (21820)------------------------------
% 0.20/0.56  % (21809)Success in time 0.199 s
%------------------------------------------------------------------------------

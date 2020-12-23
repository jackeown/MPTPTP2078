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
% DateTime   : Thu Dec  3 12:54:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  67 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 227 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,(
    k10_relat_1(sK1,sK0) != k10_relat_1(sK1,sK0) ),
    inference(superposition,[],[f20,f58])).

fof(f58,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(sK1,X0) ),
    inference(forward_demodulation,[],[f57,f29])).

fof(f29,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f28,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f26,f18])).

fof(f18,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f57,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0) ),
    inference(subsumption_resolution,[],[f56,f17])).

fof(f56,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f54,f18])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f46,f19])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f45,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k2_funct_1(X1))
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f20,plain,(
    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:19:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (16967)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.42  % (16972)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (16967)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f61])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    k10_relat_1(sK1,sK0) != k10_relat_1(sK1,sK0)),
% 0.22/0.42    inference(superposition,[],[f20,f58])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(sK1,X0)) )),
% 0.22/0.42    inference(forward_demodulation,[],[f57,f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.42    inference(subsumption_resolution,[],[f28,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    v1_relat_1(sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0,X1] : (k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0,X1] : ((k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.42    inference(negated_conjecture,[],[f5])).
% 0.22/0.42  fof(f5,conjecture,(
% 0.22/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.42    inference(subsumption_resolution,[],[f26,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    v1_funct_1(sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.22/0.42    inference(resolution,[],[f24,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    v2_funct_1(sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(flattening,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0)) )),
% 0.22/0.42    inference(subsumption_resolution,[],[f56,f17])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.42    inference(subsumption_resolution,[],[f54,f18])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_funct_1(sK1) | k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.42    inference(resolution,[],[f46,f19])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    ( ! [X2,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(subsumption_resolution,[],[f45,f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(flattening,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ( ! [X2,X1] : (~v1_relat_1(k2_funct_1(X1)) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(subsumption_resolution,[],[f42,f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ( ! [X2,X1] : (~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(resolution,[],[f25,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(flattening,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (16967)------------------------------
% 0.22/0.42  % (16967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (16967)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (16967)Memory used [KB]: 10618
% 0.22/0.42  % (16967)Time elapsed: 0.006 s
% 0.22/0.42  % (16967)------------------------------
% 0.22/0.42  % (16967)------------------------------
% 0.22/0.43  % (16966)Success in time 0.063 s
%------------------------------------------------------------------------------

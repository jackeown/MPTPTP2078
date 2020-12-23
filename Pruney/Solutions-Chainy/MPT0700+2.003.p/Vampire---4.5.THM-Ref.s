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
% DateTime   : Thu Dec  3 12:54:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  67 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 247 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,(
    k10_relat_1(sK1,sK0) != k10_relat_1(sK1,sK0) ),
    inference(superposition,[],[f17,f55])).

fof(f55,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(sK1,X0) ),
    inference(forward_demodulation,[],[f54,f26])).

fof(f26,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f25,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f25,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f23,f15])).

fof(f15,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f54,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0) ),
    inference(subsumption_resolution,[],[f53,f14])).

fof(f53,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f51,f15])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f43,f16])).

fof(f43,plain,(
    ! [X2,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f42,f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f42,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k2_funct_1(X1))
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f39,f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f22,f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f17,plain,(
    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:29 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.41  % (17161)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (17162)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (17154)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (17154)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    k10_relat_1(sK1,sK0) != k10_relat_1(sK1,sK0)),
% 0.20/0.42    inference(superposition,[],[f17,f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(sK1,X0)) )),
% 0.20/0.42    inference(forward_demodulation,[],[f54,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.20/0.42    inference(subsumption_resolution,[],[f25,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0,X1] : (k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0,X1] : ((k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.20/0.42    inference(subsumption_resolution,[],[f23,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    v1_funct_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.20/0.42    inference(resolution,[],[f21,f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    v2_funct_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f53,f14])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f51,f15])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_funct_1(sK1) | k9_relat_1(k2_funct_1(sK1),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK1)),X0) | ~v1_relat_1(sK1)) )),
% 0.20/0.42    inference(resolution,[],[f43,f16])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X2,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f42,f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ( ! [X2,X1] : (~v1_relat_1(k2_funct_1(X1)) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f39,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X2,X1] : (~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(resolution,[],[f22,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (17154)------------------------------
% 0.20/0.42  % (17154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (17154)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (17154)Memory used [KB]: 10618
% 0.20/0.42  % (17154)Time elapsed: 0.005 s
% 0.20/0.42  % (17154)------------------------------
% 0.20/0.42  % (17154)------------------------------
% 0.20/0.43  % (17153)Success in time 0.075 s
%------------------------------------------------------------------------------

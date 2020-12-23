%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  46 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 171 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f15])).

fof(f15,plain,(
    ~ v1_finset_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

% (31764)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
fof(f11,plain,
    ( ~ v1_finset_1(k2_relat_1(sK0))
    & v1_finset_1(k1_relat_1(sK0))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ~ v1_finset_1(k2_relat_1(X0))
        & v1_finset_1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v1_finset_1(k2_relat_1(sK0))
      & v1_finset_1(k1_relat_1(sK0))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      & v1_finset_1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
         => v1_finset_1(k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).

fof(f22,plain,(
    v1_finset_1(k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f20,f18])).

fof(f18,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f12,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    v1_finset_1(k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f12,f13,f14,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X1,X0))
      | ~ v1_finset_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_finset_1(X0)
       => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).

fof(f14,plain,(
    v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:43:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.40  % (31766)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (31765)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (31761)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.44  % (31770)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.44  % (31763)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (31761)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % (31759)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f22,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ~v1_finset_1(k2_relat_1(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  % (31764)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ~v1_finset_1(k2_relat_1(sK0)) & v1_finset_1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0] : (~v1_finset_1(k2_relat_1(X0)) & v1_finset_1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v1_finset_1(k2_relat_1(sK0)) & v1_finset_1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0] : (~v1_finset_1(k2_relat_1(X0)) & v1_finset_1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f5])).
% 0.21/0.44  fof(f5,plain,(
% 0.21/0.44    ? [X0] : ((~v1_finset_1(k2_relat_1(X0)) & v1_finset_1(k1_relat_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) => v1_finset_1(k2_relat_1(X0))))),
% 0.21/0.44    inference(negated_conjecture,[],[f3])).
% 0.21/0.44  fof(f3,conjecture,(
% 0.21/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) => v1_finset_1(k2_relat_1(X0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    v1_finset_1(k2_relat_1(sK0))),
% 0.21/0.44    inference(forward_demodulation,[],[f20,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f12,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    v1_relat_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_finset_1(k9_relat_1(sK0,k1_relat_1(sK0)))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f12,f13,f14,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_finset_1(k9_relat_1(X1,X0)) | ~v1_finset_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_finset_1(k9_relat_1(X1,X0)) | ~v1_finset_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1] : ((v1_finset_1(k9_relat_1(X1,X0)) | ~v1_finset_1(X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_finset_1(X0) => v1_finset_1(k9_relat_1(X1,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    v1_finset_1(k1_relat_1(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    v1_funct_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31761)------------------------------
% 0.21/0.44  % (31761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31761)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31761)Memory used [KB]: 6012
% 0.21/0.44  % (31761)Time elapsed: 0.024 s
% 0.21/0.44  % (31761)------------------------------
% 0.21/0.44  % (31761)------------------------------
% 0.21/0.44  % (31758)Success in time 0.084 s
%------------------------------------------------------------------------------

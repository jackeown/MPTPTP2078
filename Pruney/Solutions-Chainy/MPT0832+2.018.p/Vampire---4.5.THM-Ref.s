%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 116 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,sK3),sK3) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(f29,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | r1_tarski(k8_relat_1(X7,X4),X4) ) ),
    inference(resolution,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f60,plain,(
    ~ r1_tarski(k8_relat_1(sK1,sK3),sK3) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    ! [X0] :
      ( sP4(X0,sK2)
      | ~ r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f35,f18])).

fof(f35,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ r1_tarski(X10,X11)
      | sP4(X10,X12) ) ),
    inference(resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | sP4(X3,X2) ) ),
    inference(cnf_transformation,[],[f26_D])).

fof(f26_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    <=> ~ sP4(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f50,plain,(
    ~ sP4(k8_relat_1(sK1,sK3),sK2) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(superposition,[],[f19,f32])).

fof(f32,plain,(
    ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3) ),
    inference(resolution,[],[f23,f18])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f19,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP4(k8_relat_1(X0,sK3),X1) ) ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sP4(X3,X2) ) ),
    inference(general_splitting,[],[f25,f26_D])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) ),
    inference(resolution,[],[f28,f18])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(k8_relat_1(X3,X0)),X3) ) ),
    inference(resolution,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:42:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (29053)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (29052)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (29050)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.43  % (29057)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.44  % (29050)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f60,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK3),sK3)) )),
% 0.22/0.44    inference(resolution,[],[f29,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | r1_tarski(k8_relat_1(X7,X4),X4)) )),
% 0.22/0.44    inference(resolution,[],[f22,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ~r1_tarski(k8_relat_1(sK1,sK3),sK3)),
% 0.22/0.44    inference(resolution,[],[f50,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ( ! [X0] : (sP4(X0,sK2) | ~r1_tarski(X0,sK3)) )),
% 0.22/0.44    inference(resolution,[],[f35,f18])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X12,X10,X13,X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~r1_tarski(X10,X11) | sP4(X10,X12)) )),
% 0.22/0.44    inference(resolution,[],[f24,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | sP4(X3,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f26_D])).
% 0.22/0.44  fof(f26_D,plain,(
% 0.22/0.44    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) <=> ~sP4(X3,X2)) )),
% 0.22/0.44    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ~sP4(k8_relat_1(sK1,sK3),sK2)),
% 0.22/0.44    inference(resolution,[],[f43,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.44    inference(superposition,[],[f19,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)) )),
% 0.22/0.44    inference(resolution,[],[f23,f18])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP4(k8_relat_1(X0,sK3),X1)) )),
% 0.22/0.44    inference(resolution,[],[f41,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X2,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sP4(X3,X2)) )),
% 0.22/0.44    inference(general_splitting,[],[f25,f26_D])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)) )),
% 0.22/0.44    inference(resolution,[],[f28,f18])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(k8_relat_1(X3,X0)),X3)) )),
% 0.22/0.44    inference(resolution,[],[f22,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (29050)------------------------------
% 0.22/0.44  % (29050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (29050)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (29050)Memory used [KB]: 10618
% 0.22/0.44  % (29050)Time elapsed: 0.007 s
% 0.22/0.44  % (29050)------------------------------
% 0.22/0.44  % (29050)------------------------------
% 0.22/0.44  % (29045)Success in time 0.077 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 144 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f52,f70])).

fof(f70,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f66,f18])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(f66,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f58,f22])).

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

fof(f58,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f55,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f55,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK1),sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f54,f18])).

fof(f54,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,sK2)))
        | ~ r1_tarski(k7_relat_1(sK3,sK1),X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f45,f24])).

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

fof(f45,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_2
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f52,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f48,f18])).

fof(f48,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_1 ),
    inference(resolution,[],[f47,f22])).

fof(f47,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f42,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f42,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_1
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f46,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f38,f44,f40])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ) ),
    inference(forward_demodulation,[],[f37,f26])).

fof(f26,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f23,f18])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
      | ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(forward_demodulation,[],[f33,f26])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1)
      | ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (23882)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (23889)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (23882)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f71,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f46,f52,f70])).
% 0.20/0.41  fof(f70,plain,(
% 0.20/0.41    ~spl4_2),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f67])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    $false | ~spl4_2),
% 0.20/0.41    inference(resolution,[],[f66,f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.41    inference(ennf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.41    inference(negated_conjecture,[],[f7])).
% 0.20/0.41  fof(f7,conjecture,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_2),
% 0.20/0.41    inference(resolution,[],[f58,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.41  fof(f58,plain,(
% 0.20/0.41    ~v1_relat_1(sK3) | ~spl4_2),
% 0.20/0.41    inference(resolution,[],[f55,f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    ~r1_tarski(k7_relat_1(sK3,sK1),sK3) | ~spl4_2),
% 0.20/0.41    inference(resolution,[],[f54,f18])).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) | ~r1_tarski(k7_relat_1(sK3,sK1),X2)) ) | ~spl4_2),
% 0.20/0.41    inference(resolution,[],[f45,f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.41    inference(flattening,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl4_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f44])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    spl4_2 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    spl4_1),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f49])).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    $false | spl4_1),
% 0.20/0.41    inference(resolution,[],[f48,f18])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_1),
% 0.20/0.41    inference(resolution,[],[f47,f22])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    ~v1_relat_1(sK3) | spl4_1),
% 0.20/0.41    inference(resolution,[],[f42,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl4_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    spl4_1 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    ~spl4_1 | spl4_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f38,f44,f40])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)) )),
% 0.20/0.41    inference(forward_demodulation,[],[f37,f26])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.20/0.41    inference(resolution,[],[f23,f18])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.20/0.41    inference(forward_demodulation,[],[f33,f26])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(k1_relat_1(k5_relset_1(sK0,sK2,sK3,sK1)),sK1) | ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.20/0.41    inference(resolution,[],[f25,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.41    inference(flattening,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (23882)------------------------------
% 0.20/0.42  % (23882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (23882)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (23882)Memory used [KB]: 10618
% 0.20/0.42  % (23882)Time elapsed: 0.004 s
% 0.20/0.42  % (23882)------------------------------
% 0.20/0.42  % (23882)------------------------------
% 0.20/0.42  % (23888)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (23881)Success in time 0.058 s
%------------------------------------------------------------------------------

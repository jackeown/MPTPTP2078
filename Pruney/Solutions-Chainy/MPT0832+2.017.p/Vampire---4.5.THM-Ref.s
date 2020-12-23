%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 118 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :  178 ( 256 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f44,f50,f56,f60,f65,f77,f83,f94,f129,f154,f173,f279])).

fof(f279,plain,
    ( spl4_9
    | ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl4_9
    | ~ spl4_27 ),
    inference(resolution,[],[f172,f76])).

fof(f76,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_9
  <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f172,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_27
  <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f173,plain,
    ( spl4_27
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f166,f152,f92,f171])).

fof(f92,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f152,plain,
    ( spl4_24
  <=> ! [X2] : m1_subset_1(k8_relat_1(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f166,plain,
    ( ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(resolution,[],[f153,f93])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f153,plain,
    ( ! [X2] : m1_subset_1(k8_relat_1(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl4_24
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f146,f127,f152])).

fof(f127,plain,
    ( spl4_19
  <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK3),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f146,plain,
    ( ! [X2] : m1_subset_1(k8_relat_1(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_19 ),
    inference(resolution,[],[f128,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f128,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK3),k2_zfmisc_1(sK2,sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( spl4_19
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f125,f81,f41,f127])).

fof(f41,plain,
    ( spl4_3
  <=> r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f81,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK3,X0)
        | r1_tarski(k8_relat_1(X1,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f125,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK3),k2_zfmisc_1(sK2,sK0))
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f82,f43])).

fof(f43,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK3,X0)
        | r1_tarski(k8_relat_1(X1,sK3),X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f94,plain,
    ( spl4_12
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f88,f54,f92])).

fof(f54,plain,
    ( spl4_5
  <=> ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl4_5 ),
    inference(resolution,[],[f55,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f55,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f83,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f78,f58,f81])).

fof(f58,plain,
    ( spl4_6
  <=> ! [X1] : r1_tarski(k8_relat_1(X1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK3,X0)
        | r1_tarski(k8_relat_1(X1,sK3),X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f59,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f59,plain,
    ( ! [X1] : r1_tarski(k8_relat_1(X1,sK3),sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f77,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f72,f63,f30,f74])).

fof(f30,plain,
    ( spl4_1
  <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,
    ( spl4_7
  <=> ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f72,plain,
    ( ~ m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f32,f64])).

fof(f64,plain,
    ( ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f32,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f65,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f35,f63])).

fof(f35,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f61,plain,
    ( ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f60,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f52,f47,f58])).

fof(f47,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f52,plain,
    ( ! [X1] : r1_tarski(k8_relat_1(X1,sK3),sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f49,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f49,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f56,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f51,f47,f54])).

fof(f51,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f49,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f50,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f45,f35,f47])).

fof(f45,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f25,f37])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f44,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f35,f41])).

fof(f39,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f24,f37])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(f33,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f20,f30])).

fof(f20,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (32023)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (32024)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (32025)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (32022)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (32018)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (32019)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.45  % (32019)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f288,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f33,f38,f44,f50,f56,f60,f65,f77,f83,f94,f129,f154,f173,f279])).
% 0.21/0.45  fof(f279,plain,(
% 0.21/0.45    spl4_9 | ~spl4_27),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f273])).
% 0.21/0.45  fof(f273,plain,(
% 0.21/0.45    $false | (spl4_9 | ~spl4_27)),
% 0.21/0.45    inference(resolution,[],[f172,f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl4_9 <=> m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl4_27),
% 0.21/0.45    inference(avatar_component_clause,[],[f171])).
% 0.21/0.45  fof(f171,plain,(
% 0.21/0.45    spl4_27 <=> ! [X0] : m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    spl4_27 | ~spl4_12 | ~spl4_24),
% 0.21/0.45    inference(avatar_split_clause,[],[f166,f152,f92,f171])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl4_12 <=> ! [X1,X0,X2] : (~m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    spl4_24 <=> ! [X2] : m1_subset_1(k8_relat_1(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | (~spl4_12 | ~spl4_24)),
% 0.21/0.45    inference(resolution,[],[f153,f93])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl4_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f92])).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    ( ! [X2] : (m1_subset_1(k8_relat_1(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_24),
% 0.21/0.45    inference(avatar_component_clause,[],[f152])).
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    spl4_24 | ~spl4_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f146,f127,f152])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    spl4_19 <=> ! [X0] : r1_tarski(k8_relat_1(X0,sK3),k2_zfmisc_1(sK2,sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    ( ! [X2] : (m1_subset_1(k8_relat_1(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_19),
% 0.21/0.45    inference(resolution,[],[f128,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK3),k2_zfmisc_1(sK2,sK0))) ) | ~spl4_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f127])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    spl4_19 | ~spl4_3 | ~spl4_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f125,f81,f41,f127])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl4_3 <=> r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl4_10 <=> ! [X1,X0] : (~r1_tarski(sK3,X0) | r1_tarski(k8_relat_1(X1,sK3),X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK3),k2_zfmisc_1(sK2,sK0))) ) | (~spl4_3 | ~spl4_10)),
% 0.21/0.45    inference(resolution,[],[f82,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) | ~spl4_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f41])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(sK3,X0) | r1_tarski(k8_relat_1(X1,sK3),X0)) ) | ~spl4_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl4_12 | ~spl4_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f88,f54,f92])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl4_5 <=> ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl4_5),
% 0.21/0.45    inference(resolution,[],[f55,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)) ) | ~spl4_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f54])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    spl4_10 | ~spl4_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f78,f58,f81])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl4_6 <=> ! [X1] : r1_tarski(k8_relat_1(X1,sK3),sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(sK3,X0) | r1_tarski(k8_relat_1(X1,sK3),X0)) ) | ~spl4_6),
% 0.21/0.45    inference(resolution,[],[f59,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK3),sK3)) ) | ~spl4_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ~spl4_9 | spl4_1 | ~spl4_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f72,f63,f30,f74])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl4_1 <=> m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl4_7 <=> ! [X0] : k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ~m1_subset_1(k8_relat_1(sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_1 | ~spl4_7)),
% 0.21/0.45    inference(superposition,[],[f32,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0] : (k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)) ) | ~spl4_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f63])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f30])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl4_7 | ~spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f61,f35,f63])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X0] : (k8_relat_1(X0,sK3) = k6_relset_1(sK2,sK0,X0,sK3)) ) | ~spl4_2),
% 0.21/0.45    inference(resolution,[],[f27,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f35])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl4_6 | ~spl4_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f52,f47,f58])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK3),sK3)) ) | ~spl4_4),
% 0.21/0.45    inference(resolution,[],[f49,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f47])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl4_5 | ~spl4_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f51,f47,f54])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK3)),X0)) ) | ~spl4_4),
% 0.21/0.45    inference(resolution,[],[f49,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    spl4_4 | ~spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f45,f35,f47])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    v1_relat_1(sK3) | ~spl4_2),
% 0.21/0.45    inference(resolution,[],[f25,f37])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl4_3 | ~spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f39,f35,f41])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) | ~spl4_2),
% 0.21/0.45    inference(resolution,[],[f24,f37])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f35])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ~spl4_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f30])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (32019)------------------------------
% 0.21/0.45  % (32019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (32019)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (32019)Memory used [KB]: 10746
% 0.21/0.45  % (32019)Time elapsed: 0.039 s
% 0.21/0.45  % (32019)------------------------------
% 0.21/0.45  % (32019)------------------------------
% 0.21/0.46  % (32017)Success in time 0.104 s
%------------------------------------------------------------------------------

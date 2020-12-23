%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 124 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 242 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (6775)Refutation not found, incomplete strategy% (6775)------------------------------
% (6775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6775)Termination reason: Refutation not found, incomplete strategy

% (6775)Memory used [KB]: 10618
% (6775)Time elapsed: 0.121 s
% (6775)------------------------------
% (6775)------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f83,f101,f115,f120,f126])).

fof(f126,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f114,f52])).

fof(f52,plain,(
    r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f51,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(global_subsumption,[],[f25,f50])).

fof(f50,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f35,f45])).

fof(f45,plain,(
    k1_relset_1(sK2,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f34,f25])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

fof(f114,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_8
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f120,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f111,f41])).

fof(f41,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f111,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f115,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f107,f68,f113,f110])).

fof(f68,plain,
    ( spl4_3
  <=> r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f107,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(resolution,[],[f97,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl4_3 ),
    inference(resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f73,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2)
    | spl4_3 ),
    inference(backward_demodulation,[],[f69,f55])).

fof(f55,plain,(
    ! [X9] : k6_relset_1(sK2,sK0,X9,sK3) = k8_relat_1(X9,sK3) ),
    inference(resolution,[],[f37,f25])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f69,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f101,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f98,f41])).

fof(f98,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2 ),
    inference(resolution,[],[f74,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f74,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f66,f55])).

fof(f66,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_2
  <=> r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f83,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f79,f41])).

fof(f79,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f75,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f75,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | spl4_1 ),
    inference(backward_demodulation,[],[f63,f55])).

fof(f63,plain,
    ( ~ v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_1
  <=> v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f70,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f68,f65,f62])).

fof(f56,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2)
    | ~ r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1)
    | ~ v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:23:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (6777)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % (6785)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.54  % (6772)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.54  % (6770)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.54  % (6791)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.55  % (6777)Refutation not found, incomplete strategy% (6777)------------------------------
% 0.22/0.55  % (6777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6777)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6777)Memory used [KB]: 10490
% 0.22/0.55  % (6777)Time elapsed: 0.104 s
% 0.22/0.55  % (6777)------------------------------
% 0.22/0.55  % (6777)------------------------------
% 0.22/0.55  % (6781)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.55  % (6775)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.55  % (6768)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.55  % (6792)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.55  % (6780)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.55  % (6781)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  % (6775)Refutation not found, incomplete strategy% (6775)------------------------------
% 0.22/0.55  % (6775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6775)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6775)Memory used [KB]: 10618
% 0.22/0.55  % (6775)Time elapsed: 0.121 s
% 0.22/0.55  % (6775)------------------------------
% 0.22/0.55  % (6775)------------------------------
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f70,f83,f101,f115,f120,f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    spl4_8),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f124])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    $false | spl4_8),
% 0.22/0.55    inference(resolution,[],[f114,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    r1_tarski(k1_relat_1(sK3),sK2)),
% 0.22/0.55    inference(resolution,[],[f51,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.22/0.55    inference(global_subsumption,[],[f25,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.55    inference(superposition,[],[f35,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    k1_relset_1(sK2,sK0,sK3) = k1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f34,f25])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.55    inference(negated_conjecture,[],[f11])).
% 0.22/0.55  fof(f11,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK3),sK2) | spl4_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f113])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    spl4_8 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    spl4_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    $false | spl4_7),
% 0.22/0.55    inference(resolution,[],[f111,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f33,f25])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | spl4_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f110])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    spl4_7 <=> v1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ~spl4_7 | ~spl4_8 | spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f107,f68,f113,f110])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    spl4_3 <=> r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | spl4_3),
% 0.22/0.55    inference(resolution,[],[f97,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),X0) | ~r1_tarski(X0,sK2)) ) | spl4_3),
% 0.22/0.55    inference(resolution,[],[f73,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) | spl4_3),
% 0.22/0.55    inference(backward_demodulation,[],[f69,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X9] : (k6_relset_1(sK2,sK0,X9,sK3) = k8_relat_1(X9,sK3)) )),
% 0.22/0.55    inference(resolution,[],[f37,f25])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2) | spl4_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    spl4_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    $false | spl4_2),
% 0.22/0.55    inference(resolution,[],[f98,f41])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | spl4_2),
% 0.22/0.55    inference(resolution,[],[f74,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) | spl4_2),
% 0.22/0.55    inference(backward_demodulation,[],[f66,f55])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1) | spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    spl4_2 <=> r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    spl4_1),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    $false | spl4_1),
% 0.22/0.55    inference(resolution,[],[f79,f41])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | spl4_1),
% 0.22/0.55    inference(resolution,[],[f75,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ~v1_relat_1(k8_relat_1(sK1,sK3)) | spl4_1),
% 0.22/0.55    inference(backward_demodulation,[],[f63,f55])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ~v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)) | spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    spl4_1 <=> v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f56,f68,f65,f62])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2) | ~r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1) | ~v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))),
% 0.22/0.55    inference(resolution,[],[f32,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (6781)------------------------------
% 0.22/0.55  % (6781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6781)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (6781)Memory used [KB]: 10618
% 0.22/0.55  % (6781)Time elapsed: 0.124 s
% 0.22/0.55  % (6781)------------------------------
% 0.22/0.55  % (6781)------------------------------
% 0.22/0.55  % (6767)Success in time 0.186 s
%------------------------------------------------------------------------------

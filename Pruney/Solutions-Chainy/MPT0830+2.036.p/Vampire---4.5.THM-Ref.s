%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 114 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 231 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f41,f60,f72,f76,f80,f89])).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,(
    ! [X0] : v5_relat_1(k7_relat_1(sK3,X0),sK2) ),
    inference(global_subsumption,[],[f21,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v5_relat_1(k7_relat_1(sK3,X0),sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    inference(superposition,[],[f62,f45])).

fof(f45,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f30,f21])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f62,plain,(
    ! [X6,X8,X7,X5] :
      ( v5_relat_1(k5_relset_1(X6,X7,X5,X8),X7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relset_1)).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f79,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_6
  <=> v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f80,plain,
    ( ~ spl4_6
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f67,f55,f52,f78])).

fof(f52,plain,
    ( spl4_3
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f55,plain,
    ( spl4_4
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2)
    | spl4_4 ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

% (30048)Refutation not found, incomplete strategy% (30048)------------------------------
% (30048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30048)Termination reason: Refutation not found, incomplete strategy

% (30048)Memory used [KB]: 10490
% (30048)Time elapsed: 0.116 s
% (30048)------------------------------
% (30048)------------------------------
fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f56,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f76,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f70,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_subsumption,[],[f21,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK3,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    inference(superposition,[],[f65,f45])).

fof(f65,plain,(
    ! [X12,X10,X11,X9] :
      ( v1_relat_1(k5_relset_1(X10,X11,X9,X12))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(global_subsumption,[],[f24,f63])).

fof(f63,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_relat_1(k2_zfmisc_1(X10,X11))
      | v1_relat_1(k5_relset_1(X10,X11,X9,X12)) ) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f24,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,
    ( ~ spl4_1
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl4_1
    | spl4_5 ),
    inference(resolution,[],[f68,f35])).

fof(f35,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f68,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(resolution,[],[f59,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f59,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_5
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f60,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f50,f58,f55,f52])).

fof(f50,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f28,f46])).

fof(f46,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f22,f45])).

fof(f22,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f39,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f32,f37,f34])).

fof(f32,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f23,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (30051)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.46  % (30071)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.46  % (30069)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.48  % (30071)Refutation not found, incomplete strategy% (30071)------------------------------
% 0.22/0.48  % (30071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (30071)Memory used [KB]: 10618
% 0.22/0.48  % (30071)Time elapsed: 0.094 s
% 0.22/0.48  % (30071)------------------------------
% 0.22/0.48  % (30071)------------------------------
% 0.22/0.49  % (30070)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (30061)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (30048)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (30046)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (30045)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (30049)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (30058)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (30064)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (30068)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (30063)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (30059)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (30065)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (30066)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (30059)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f39,f41,f60,f72,f76,f80,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl4_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    $false | spl4_6),
% 0.22/0.52    inference(resolution,[],[f79,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),sK2)) )),
% 0.22/0.52    inference(global_subsumption,[],[f21,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))) )),
% 0.22/0.52    inference(superposition,[],[f62,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.52    inference(resolution,[],[f30,f21])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X6,X8,X7,X5] : (v5_relat_1(k5_relset_1(X6,X7,X5,X8),X7) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.22/0.52    inference(resolution,[],[f31,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relset_1)).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ~v5_relat_1(k7_relat_1(sK3,sK1),sK2) | spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl4_6 <=> v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ~spl4_6 | ~spl4_3 | spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f67,f55,f52,f78])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl4_3 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl4_4 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v5_relat_1(k7_relat_1(sK3,sK1),sK2) | spl4_4),
% 0.22/0.52    inference(resolution,[],[f56,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  % (30048)Refutation not found, incomplete strategy% (30048)------------------------------
% 0.22/0.52  % (30048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30048)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30048)Memory used [KB]: 10490
% 0.22/0.52  % (30048)Time elapsed: 0.116 s
% 0.22/0.52  % (30048)------------------------------
% 0.22/0.52  % (30048)------------------------------
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl4_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    $false | spl4_3),
% 0.22/0.52    inference(resolution,[],[f70,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f52])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.22/0.52    inference(global_subsumption,[],[f21,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))) )),
% 0.22/0.52    inference(superposition,[],[f65,f45])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X12,X10,X11,X9] : (v1_relat_1(k5_relset_1(X10,X11,X9,X12)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 0.22/0.52    inference(global_subsumption,[],[f24,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_relat_1(k2_zfmisc_1(X10,X11)) | v1_relat_1(k5_relset_1(X10,X11,X9,X12))) )),
% 0.22/0.52    inference(resolution,[],[f31,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~spl4_1 | spl4_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    $false | (~spl4_1 | spl4_5)),
% 0.22/0.52    inference(resolution,[],[f68,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    spl4_1 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | spl4_5),
% 0.22/0.52    inference(resolution,[],[f59,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl4_5 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f50,f58,f55,f52])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.22/0.52    inference(resolution,[],[f28,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    inference(backward_demodulation,[],[f22,f45])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    spl4_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    $false | spl4_2),
% 0.22/0.52    inference(resolution,[],[f38,f24])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl4_1 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f32,f37,f34])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f23,f21])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (30059)------------------------------
% 0.22/0.52  % (30059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30059)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (30059)Memory used [KB]: 10618
% 0.22/0.52  % (30059)Time elapsed: 0.086 s
% 0.22/0.52  % (30059)------------------------------
% 0.22/0.52  % (30059)------------------------------
% 0.22/0.52  % (30053)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (30052)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (30052)Refutation not found, incomplete strategy% (30052)------------------------------
% 0.22/0.52  % (30052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30052)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30052)Memory used [KB]: 6012
% 0.22/0.52  % (30052)Time elapsed: 0.084 s
% 0.22/0.52  % (30052)------------------------------
% 0.22/0.52  % (30052)------------------------------
% 0.22/0.52  % (30047)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  % (30041)Success in time 0.162 s
%------------------------------------------------------------------------------

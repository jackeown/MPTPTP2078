%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 230 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f44,f66,f74,f82,f91,f102,f121])).

fof(f121,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f62])).

fof(f62,plain,
    ( ! [X13] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X13,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_3
  <=> ! [X13] : ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X13,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(global_subsumption,[],[f22,f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    inference(superposition,[],[f33,f48])).

fof(f48,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f32,f22])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(f102,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl4_7 ),
    inference(resolution,[],[f81,f47])).

fof(f47,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f81,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_7
  <=> ! [X0] : ~ v4_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f91,plain,
    ( ~ spl4_1
    | spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f89,f69,f80,f37])).

fof(f37,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69,plain,
    ( spl4_5
  <=> v4_relat_1(k7_relat_1(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_5 ),
    inference(resolution,[],[f70,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f70,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f82,plain,
    ( ~ spl4_1
    | spl4_7
    | spl4_6 ),
    inference(avatar_split_clause,[],[f77,f72,f80,f37])).

fof(f72,plain,
    ( spl4_6
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_6 ),
    inference(resolution,[],[f73,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f72])).

% (12158)Refutation not found, incomplete strategy% (12158)------------------------------
% (12158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f74,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f67,f64,f72,f69])).

% (12158)Termination reason: Refutation not found, incomplete strategy

fof(f64,plain,
    ( spl4_4
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

% (12158)Memory used [KB]: 10490
fof(f67,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl4_4 ),
    inference(resolution,[],[f65,f27])).

% (12158)Time elapsed: 0.106 s
% (12158)------------------------------
% (12158)------------------------------
fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f65,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f59,f64,f61])).

fof(f59,plain,(
    ! [X13] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
      | ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X13,sK2))) ) ),
    inference(resolution,[],[f34,f49])).

fof(f49,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f23,f48])).

fof(f23,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f41,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f42,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f35,f40,f37])).

fof(f35,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f24,f22])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (12171)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.46  % (12163)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.47  % (12154)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (12154)Refutation not found, incomplete strategy% (12154)------------------------------
% 0.20/0.47  % (12154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12154)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (12154)Memory used [KB]: 6012
% 0.20/0.47  % (12154)Time elapsed: 0.061 s
% 0.20/0.47  % (12154)------------------------------
% 0.20/0.47  % (12154)------------------------------
% 0.20/0.48  % (12147)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.49  % (12148)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (12168)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.49  % (12166)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.49  % (12167)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (12169)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.49  % (12151)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (12149)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (12150)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (12150)Refutation not found, incomplete strategy% (12150)------------------------------
% 0.20/0.50  % (12150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12150)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12150)Memory used [KB]: 10490
% 0.20/0.50  % (12150)Time elapsed: 0.092 s
% 0.20/0.50  % (12150)------------------------------
% 0.20/0.50  % (12150)------------------------------
% 0.20/0.50  % (12170)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (12152)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (12153)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (12156)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (12159)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (12160)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (12165)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (12158)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (12160)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f42,f44,f66,f74,f82,f91,f102,f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ~spl4_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    $false | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f55,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X13] : (~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X13,sK2)))) ) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl4_3 <=> ! [X13] : ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X13,sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))) )),
% 0.20/0.51    inference(global_subsumption,[],[f22,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))) )),
% 0.20/0.51    inference(superposition,[],[f33,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.20/0.51    inference(resolution,[],[f32,f22])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~spl4_7),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    $false | ~spl4_7),
% 0.20/0.51    inference(resolution,[],[f81,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v4_relat_1(sK3,sK0)),
% 0.20/0.51    inference(resolution,[],[f28,f22])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl4_7 <=> ! [X0] : ~v4_relat_1(sK3,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ~spl4_1 | spl4_7 | spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f89,f69,f80,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    spl4_1 <=> v1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl4_5 <=> v4_relat_1(k7_relat_1(sK3,sK1),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_5),
% 0.20/0.51    inference(resolution,[],[f70,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ~spl4_1 | spl4_7 | spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f77,f72,f80,f37])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl4_6 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_6),
% 0.20/0.51    inference(resolution,[],[f73,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f72])).
% 0.20/0.51  % (12158)Refutation not found, incomplete strategy% (12158)------------------------------
% 0.20/0.51  % (12158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ~spl4_5 | ~spl4_6 | spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f67,f64,f72,f69])).
% 0.20/0.51  % (12158)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl4_4 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  % (12158)Memory used [KB]: 10490
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | spl4_4),
% 0.20/0.51    inference(resolution,[],[f65,f27])).
% 0.20/0.51  % (12158)Time elapsed: 0.106 s
% 0.20/0.51  % (12158)------------------------------
% 0.20/0.51  % (12158)------------------------------
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl4_3 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f64,f61])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X13] : (~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(X13,sK2)))) )),
% 0.20/0.51    inference(resolution,[],[f34,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.51    inference(backward_demodulation,[],[f23,f48])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    $false | spl4_2),
% 0.20/0.51    inference(resolution,[],[f41,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK0,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f40,f37])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3)),
% 0.20/0.51    inference(resolution,[],[f24,f22])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (12160)------------------------------
% 0.20/0.51  % (12160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12160)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (12160)Memory used [KB]: 10618
% 0.20/0.51  % (12160)Time elapsed: 0.112 s
% 0.20/0.51  % (12160)------------------------------
% 0.20/0.51  % (12160)------------------------------
% 0.20/0.51  % (12161)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (12145)Success in time 0.158 s
%------------------------------------------------------------------------------

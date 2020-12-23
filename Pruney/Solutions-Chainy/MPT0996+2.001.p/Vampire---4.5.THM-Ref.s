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
% DateTime   : Thu Dec  3 13:03:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 (  99 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :  163 ( 229 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f58,f63,f73,f79,f85,f87,f93,f99,f102])).

fof(f102,plain,
    ( spl4_9
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl4_9
    | ~ spl4_12 ),
    inference(resolution,[],[f98,f78])).

fof(f78,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_9
  <=> r1_tarski(k9_relat_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f98,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_12
  <=> ! [X0] : r1_tarski(k9_relat_1(sK3,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f99,plain,
    ( spl4_12
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f95,f91,f66,f97])).

fof(f66,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f91,plain,
    ( spl4_11
  <=> ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,k2_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f95,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),sK1)
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f94,f67])).

fof(f67,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f94,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK3,X0),sK1)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_11 ),
    inference(resolution,[],[f92,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK3))
        | r1_tarski(X0,sK1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f89,f70,f91])).

fof(f70,plain,
    ( spl4_8
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f89,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,k2_relat_1(sK3)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f72,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f87,plain,
    ( ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_10
  <=> ! [X1,X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f85,plain,
    ( spl4_10
    | spl4_7 ),
    inference(avatar_split_clause,[],[f81,f66,f83])).

fof(f81,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_7 ),
    inference(resolution,[],[f68,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f68,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f79,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f74,f61,f33,f76])).

fof(f33,plain,
    ( spl4_1
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,
    ( spl4_6
  <=> ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f74,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),sK1)
    | spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f35,f62])).

fof(f62,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f35,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f73,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f64,f55,f70,f66])).

fof(f55,plain,
    ( spl4_5
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f64,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f57,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f57,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f63,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f59,f38,f61])).

fof(f59,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_2 ),
    inference(resolution,[],[f31,f40])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f58,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f38,f55])).

fof(f53,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f30,f40])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

fof(f36,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    ~ r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 15:04:44 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.40  % (32304)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.41  % (32303)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.41  % (32296)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.19/0.41  % (32301)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (32296)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f107,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f36,f41,f58,f63,f73,f79,f85,f87,f93,f99,f102])).
% 0.19/0.42  fof(f102,plain,(
% 0.19/0.42    spl4_9 | ~spl4_12),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f100])).
% 0.19/0.42  fof(f100,plain,(
% 0.19/0.42    $false | (spl4_9 | ~spl4_12)),
% 0.19/0.42    inference(resolution,[],[f98,f78])).
% 0.19/0.42  fof(f78,plain,(
% 0.19/0.42    ~r1_tarski(k9_relat_1(sK3,sK2),sK1) | spl4_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f76])).
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    spl4_9 <=> r1_tarski(k9_relat_1(sK3,sK2),sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.42  fof(f98,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),sK1)) ) | ~spl4_12),
% 0.19/0.42    inference(avatar_component_clause,[],[f97])).
% 0.19/0.42  fof(f97,plain,(
% 0.19/0.42    spl4_12 <=> ! [X0] : r1_tarski(k9_relat_1(sK3,X0),sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.42  fof(f99,plain,(
% 0.19/0.42    spl4_12 | ~spl4_7 | ~spl4_11),
% 0.19/0.42    inference(avatar_split_clause,[],[f95,f91,f66,f97])).
% 0.19/0.42  fof(f66,plain,(
% 0.19/0.42    spl4_7 <=> v1_relat_1(sK3)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.42  fof(f91,plain,(
% 0.19/0.42    spl4_11 <=> ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,k2_relat_1(sK3)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.42  fof(f95,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),sK1)) ) | (~spl4_7 | ~spl4_11)),
% 0.19/0.42    inference(subsumption_resolution,[],[f94,f67])).
% 0.19/0.42  fof(f67,plain,(
% 0.19/0.42    v1_relat_1(sK3) | ~spl4_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f66])).
% 0.19/0.42  fof(f94,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),sK1) | ~v1_relat_1(sK3)) ) | ~spl4_11),
% 0.19/0.42    inference(resolution,[],[f92,f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.19/0.42  fof(f92,plain,(
% 0.19/0.42    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK3)) | r1_tarski(X0,sK1)) ) | ~spl4_11),
% 0.19/0.42    inference(avatar_component_clause,[],[f91])).
% 0.19/0.42  fof(f93,plain,(
% 0.19/0.42    spl4_11 | ~spl4_8),
% 0.19/0.42    inference(avatar_split_clause,[],[f89,f70,f91])).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    spl4_8 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.42  fof(f89,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,k2_relat_1(sK3))) ) | ~spl4_8),
% 0.19/0.42    inference(resolution,[],[f72,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(superposition,[],[f27,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    r1_tarski(k2_relat_1(sK3),sK1) | ~spl4_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f70])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    ~spl4_2 | ~spl4_10),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f86])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    $false | (~spl4_2 | ~spl4_10)),
% 0.20/0.42    inference(resolution,[],[f84,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f83])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    spl4_10 <=> ! [X1,X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    spl4_10 | spl4_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f81,f66,f83])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_7),
% 0.20/0.42    inference(resolution,[],[f68,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    ~v1_relat_1(sK3) | spl4_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ~spl4_9 | spl4_1 | ~spl4_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f74,f61,f33,f76])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl4_1 <=> r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl4_6 <=> ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ~r1_tarski(k9_relat_1(sK3,sK2),sK1) | (spl4_1 | ~spl4_6)),
% 0.20/0.42    inference(superposition,[],[f35,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1) | spl4_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f33])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ~spl4_7 | spl4_8 | ~spl4_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f64,f55,f70,f66])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl4_5 <=> v5_relat_1(sK3,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl4_5),
% 0.20/0.42    inference(resolution,[],[f57,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    v5_relat_1(sK3,sK1) | ~spl4_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f55])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl4_6 | ~spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f59,f38,f61])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_2),
% 0.20/0.42    inference(resolution,[],[f31,f40])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl4_5 | ~spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f53,f38,f55])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    v5_relat_1(sK3,sK1) | ~spl4_2),
% 0.20/0.42    inference(resolution,[],[f30,f40])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f38])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ~spl4_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f33])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ~r1_tarski(k7_relset_1(sK0,sK1,sK3,sK2),sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (32296)------------------------------
% 0.20/0.42  % (32296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (32296)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (32296)Memory used [KB]: 10618
% 0.20/0.42  % (32296)Time elapsed: 0.007 s
% 0.20/0.42  % (32296)------------------------------
% 0.20/0.42  % (32296)------------------------------
% 0.20/0.42  % (32294)Success in time 0.07 s
%------------------------------------------------------------------------------

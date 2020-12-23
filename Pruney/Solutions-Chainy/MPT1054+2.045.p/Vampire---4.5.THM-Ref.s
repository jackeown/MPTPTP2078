%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 125 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  189 ( 271 expanded)
%              Number of equality atoms :   47 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f53,f57,f62,f66,f70,f77,f85,f93,f97,f103,f106])).

fof(f106,plain,
    ( spl2_6
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl2_6
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f104,f76])).

fof(f76,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_9
  <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f104,plain,
    ( sK1 != k9_relat_1(k6_partfun1(sK0),sK1)
    | spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f61,f102])).

fof(f102,plain,
    ( ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_14
  <=> ! [X1,X0] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f61,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_6
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f103,plain,
    ( spl2_14
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f99,f95,f91,f64,f101])).

fof(f64,plain,
    ( spl2_7
  <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f91,plain,
    ( spl2_12
  <=> ! [X1,X3,X0,X2] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f95,plain,
    ( spl2_13
  <=> ! [X1,X0] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f99,plain,
    ( ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1)
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f98,f96])).

fof(f96,plain,
    ( ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f98,plain,
    ( ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,
    ( ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f92,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f97,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f89,f83,f55,f46,f42,f38,f95])).

fof(f38,plain,
    ( spl2_1
  <=> ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f46,plain,
    ( spl2_3
  <=> ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f55,plain,
    ( spl2_5
  <=> ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f83,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f89,plain,
    ( ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f88,f56])).

fof(f56,plain,
    ( ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f88,plain,
    ( ! [X0,X1] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_partfun1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1)
        | ~ v1_relat_1(k6_partfun1(X0)) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f39,plain,
    ( ! [X0] : v1_funct_1(k6_partfun1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1)
        | ~ v1_funct_1(k6_partfun1(X0))
        | ~ v1_relat_1(k6_partfun1(X0)) )
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f84,f47])).

fof(f47,plain,
    ( ! [X0] : v2_funct_1(k6_partfun1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(X1)
        | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f93,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f29,f91])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f85,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f28,f83])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f77,plain,
    ( spl2_9
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f71,f68,f50,f74])).

fof(f50,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f68,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k9_relat_1(k6_partfun1(X0),X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f71,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k9_relat_1(k6_partfun1(X0),X1) = X1 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f36,f68])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f27,f20])).

fof(f20,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f66,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f62,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f19,f59])).

fof(f19,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f57,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f21,f20,f20])).

fof(f21,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f50])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f34,f46])).

fof(f34,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f26,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f44,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f42])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f40,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f32,f38])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f24,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (7387)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (7384)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (7377)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (7384)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f40,f44,f48,f53,f57,f62,f66,f70,f77,f85,f93,f97,f103,f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl2_6 | ~spl2_9 | ~spl2_14),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    $false | (spl2_6 | ~spl2_9 | ~spl2_14)),
% 0.22/0.48    inference(subsumption_resolution,[],[f104,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) | ~spl2_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl2_9 <=> sK1 = k9_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    sK1 != k9_relat_1(k6_partfun1(sK0),sK1) | (spl2_6 | ~spl2_14)),
% 0.22/0.48    inference(superposition,[],[f61,f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1)) ) | ~spl2_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    spl2_14 <=> ! [X1,X0] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl2_6 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    spl2_14 | ~spl2_7 | ~spl2_12 | ~spl2_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f99,f95,f91,f64,f101])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl2_7 <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl2_12 <=> ! [X1,X3,X0,X2] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl2_13 <=> ! [X1,X0] : k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k9_relat_1(k6_partfun1(X0),X1)) ) | (~spl2_7 | ~spl2_12 | ~spl2_13)),
% 0.22/0.48    inference(forward_demodulation,[],[f98,f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) ) | ~spl2_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) ) | (~spl2_7 | ~spl2_12)),
% 0.22/0.48    inference(resolution,[],[f92,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl2_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl2_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f91])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    spl2_13 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f89,f83,f55,f46,f42,f38,f95])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl2_1 <=> ! [X0] : v1_funct_1(k6_partfun1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl2_2 <=> ! [X0] : v1_relat_1(k6_partfun1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl2_3 <=> ! [X0] : v2_funct_1(k6_partfun1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl2_5 <=> ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl2_11 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_11)),
% 0.22/0.48    inference(forward_demodulation,[],[f88,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) ) | ~spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f55])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_11)),
% 0.22/0.48    inference(subsumption_resolution,[],[f87,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) ) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1) | ~v1_relat_1(k6_partfun1(X0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_11)),
% 0.22/0.48    inference(subsumption_resolution,[],[f86,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) ) | ~spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f38])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = k10_relat_1(k2_funct_1(k6_partfun1(X0)),X1) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) ) | (~spl2_3 | ~spl2_11)),
% 0.22/0.48    inference(resolution,[],[f84,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) ) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl2_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl2_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f91])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl2_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f83])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl2_9 | ~spl2_4 | ~spl2_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f71,f68,f50,f74])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl2_8 <=> ! [X1,X0] : (k9_relat_1(k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    sK1 = k9_relat_1(k6_partfun1(sK0),sK1) | (~spl2_4 | ~spl2_8)),
% 0.22/0.48    inference(resolution,[],[f69,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = X1) ) | ~spl2_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl2_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f68])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f27,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl2_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f64])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f22,f20])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ~spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f59])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl2_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f55])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f21,f20,f20])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl2_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f50])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f46])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f26,f20])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f42])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f23,f20])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f38])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f24,f20])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7384)------------------------------
% 0.22/0.48  % (7384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7384)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7384)Memory used [KB]: 6140
% 0.22/0.48  % (7384)Time elapsed: 0.045 s
% 0.22/0.48  % (7384)------------------------------
% 0.22/0.48  % (7384)------------------------------
% 0.22/0.48  % (7376)Success in time 0.119 s
%------------------------------------------------------------------------------

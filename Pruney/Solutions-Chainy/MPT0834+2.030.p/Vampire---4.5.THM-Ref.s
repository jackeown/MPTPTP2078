%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 177 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  287 ( 421 expanded)
%              Number of equality atoms :   70 (  96 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f67,f88,f94,f102,f117,f129,f137,f140,f158,f172,f178,f200,f216,f224])).

fof(f224,plain,
    ( ~ spl3_6
    | ~ spl3_1
    | spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f223,f175,f64,f55,f99])).

fof(f99,plain,
    ( spl3_6
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( spl3_3
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f175,plain,
    ( spl3_14
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f223,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | ~ spl3_1
    | spl3_3
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f222,f177])).

fof(f177,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f222,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | ~ spl3_1
    | spl3_3 ),
    inference(forward_demodulation,[],[f66,f107])).

fof(f107,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f66,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f216,plain,
    ( ~ spl3_1
    | ~ spl3_9
    | spl3_12
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_9
    | spl3_12
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f57,f128,f157,f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_relat_1(sK2) = k10_relat_1(sK2,X0)
        | ~ r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) )
    | ~ spl3_17 ),
    inference(resolution,[],[f199,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f199,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK2,X0)
        | ~ r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
        | k1_relat_1(sK2) = k10_relat_1(sK2,X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
        | ~ v5_relat_1(sK2,X0)
        | k1_relat_1(sK2) = k10_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f157,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_12
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f128,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_9
  <=> ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f200,plain,
    ( ~ spl3_8
    | spl3_17
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f195,f135,f198,f123])).

fof(f123,plain,
    ( spl3_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f135,plain,
    ( spl3_11
  <=> ! [X2] :
        ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X2))
        | ~ r1_tarski(k2_relat_1(sK2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
        | k1_relat_1(sK2) = k10_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2)
        | ~ v5_relat_1(sK2,X0) )
    | ~ spl3_11 ),
    inference(resolution,[],[f162,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

% (19768)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
        | k1_relat_1(sK2) = k10_relat_1(sK2,X0) )
    | ~ spl3_11 ),
    inference(resolution,[],[f136,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f136,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X2))
        | ~ r1_tarski(k2_relat_1(sK2),X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f178,plain,
    ( spl3_14
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f173,f169,f123,f175])).

fof(f169,plain,
    ( spl3_13
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f173,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(superposition,[],[f145,f171])).

fof(f171,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f145,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)
    | ~ spl3_8 ),
    inference(resolution,[],[f124,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f124,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f172,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f167,f123,f55,f169])).

fof(f167,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f150,f57])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK2 = k7_relat_1(sK2,X0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f144,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f144,plain,
    ( ! [X2] :
        ( ~ v4_relat_1(sK2,X2)
        | sK2 = k7_relat_1(sK2,X2) )
    | ~ spl3_8 ),
    inference(resolution,[],[f124,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f158,plain,
    ( ~ spl3_12
    | ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f153,f91,f55,f155])).

fof(f91,plain,
    ( spl3_5
  <=> k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f153,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | ~ spl3_1
    | spl3_5 ),
    inference(superposition,[],[f93,f141])).

fof(f141,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f51,f57])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f93,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f91])).

% (19766)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f140,plain,
    ( ~ spl3_1
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl3_1
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f36,f57,f125,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f137,plain,
    ( ~ spl3_8
    | spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f120,f114,f135,f123])).

fof(f114,plain,
    ( spl3_7
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f120,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X2))
        | ~ r1_tarski(k2_relat_1(sK2),X2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(superposition,[],[f45,f116])).

fof(f116,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f129,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f118,f114,f127,f123])).

fof(f118,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(superposition,[],[f38,f116])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f117,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f112,f55,f114])).

fof(f112,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f108,f57])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f36])).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k1_relat_1(X2) = k10_relat_1(X2,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f34,f35])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (19767)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f102,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f97,f55,f99])).

fof(f97,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f47,f57])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f94,plain,
    ( ~ spl3_5
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f89,f85,f60,f91])).

fof(f60,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f85,plain,
    ( spl3_4
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f89,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f62,f87])).

fof(f87,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f62,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f88,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f83,f55,f85])).

fof(f83,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f46,f57])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f67,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f64,f60])).

fof(f32,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

% (19788)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f58,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (19781)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.48  % (19789)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.49  % (19781)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f58,f67,f88,f94,f102,f117,f129,f137,f140,f158,f172,f178,f200,f216,f224])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ~spl3_6 | ~spl3_1 | spl3_3 | ~spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f223,f175,f64,f55,f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl3_6 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_3 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    spl3_14 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | (~spl3_1 | spl3_3 | ~spl3_14)),
% 0.20/0.49    inference(forward_demodulation,[],[f222,f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f175])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | (~spl3_1 | spl3_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f66,f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X0] : (k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f50,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f55])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f64])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_9 | spl3_12 | ~spl3_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f214])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_9 | spl3_12 | ~spl3_17)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f57,f128,f157,f201])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relat_1(sK2) = k10_relat_1(sK2,X0) | ~r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))) ) | ~spl3_17),
% 0.20/0.49    inference(resolution,[],[f199,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    ( ! [X0] : (~v5_relat_1(sK2,X0) | ~r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) | k1_relat_1(sK2) = k10_relat_1(sK2,X0)) ) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f198])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    spl3_17 <=> ! [X0] : (~r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) | ~v5_relat_1(sK2,X0) | k1_relat_1(sK2) = k10_relat_1(sK2,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f155])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    spl3_12 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl3_9 <=> ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    ~spl3_8 | spl3_17 | ~spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f195,f135,f198,f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl3_8 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl3_11 <=> ! [X2] : (r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X2)) | ~r1_tarski(k2_relat_1(sK2),X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) | k1_relat_1(sK2) = k10_relat_1(sK2,X0) | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,X0)) ) | ~spl3_11),
% 0.20/0.49    inference(resolution,[],[f162,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  % (19768)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) | k1_relat_1(sK2) = k10_relat_1(sK2,X0)) ) | ~spl3_11),
% 0.20/0.49    inference(resolution,[],[f136,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X2] : (r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X2)) | ~r1_tarski(k2_relat_1(sK2),X2)) ) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f135])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl3_14 | ~spl3_8 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f173,f169,f123,f175])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    spl3_13 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | (~spl3_8 | ~spl3_13)),
% 0.20/0.49    inference(superposition,[],[f145,f171])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    sK2 = k7_relat_1(sK2,sK0) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f169])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) ) | ~spl3_8),
% 0.20/0.49    inference(resolution,[],[f124,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f123])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    spl3_13 | ~spl3_1 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f167,f123,f55,f169])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    sK2 = k7_relat_1(sK2,sK0) | (~spl3_1 | ~spl3_8)),
% 0.20/0.49    inference(resolution,[],[f150,f57])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = k7_relat_1(sK2,X0)) ) | ~spl3_8),
% 0.20/0.49    inference(resolution,[],[f144,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X2] : (~v4_relat_1(sK2,X2) | sK2 = k7_relat_1(sK2,X2)) ) | ~spl3_8),
% 0.20/0.49    inference(resolution,[],[f124,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ~spl3_12 | ~spl3_1 | spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f153,f91,f55,f155])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_5 <=> k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | (~spl3_1 | spl3_5)),
% 0.20/0.49    inference(superposition,[],[f93,f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) ) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f51,f57])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f91])).
% 0.20/0.49  % (19766)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ~spl3_1 | spl3_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    $false | (~spl3_1 | spl3_8)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f36,f57,f125,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f123])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ~spl3_8 | spl3_11 | ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f120,f114,f135,f123])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl3_7 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X2] : (r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X2)) | ~r1_tarski(k2_relat_1(sK2),X2) | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 0.20/0.49    inference(superposition,[],[f45,f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ~spl3_8 | spl3_9 | ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f118,f114,f127,f123])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 0.20/0.49    inference(superposition,[],[f38,f116])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl3_7 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f112,f55,f114])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f108,f57])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.49    inference(resolution,[],[f69,f36])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~v1_relat_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k1_relat_1(X2) = k10_relat_1(X2,k2_relat_1(X2))) )),
% 0.20/0.49    inference(resolution,[],[f34,f35])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  % (19767)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl3_6 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f97,f55,f99])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f47,f57])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ~spl3_5 | spl3_2 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f89,f85,f60,f91])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_4 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | (spl3_2 | ~spl3_4)),
% 0.20/0.49    inference(backward_demodulation,[],[f62,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f60])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_4 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f83,f55,f85])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f46,f57])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ~spl3_2 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f64,f60])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % (19788)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f15])).
% 0.20/0.49  fof(f15,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f55])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (19781)------------------------------
% 0.20/0.49  % (19781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19781)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (19781)Memory used [KB]: 6268
% 0.20/0.49  % (19781)Time elapsed: 0.094 s
% 0.20/0.49  % (19781)------------------------------
% 0.20/0.49  % (19781)------------------------------
% 0.20/0.49  % (19780)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (19765)Success in time 0.14 s
%------------------------------------------------------------------------------

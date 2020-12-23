%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 244 expanded)
%              Number of leaves         :   28 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  379 ( 877 expanded)
%              Number of equality atoms :   49 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f86,f94,f102,f115,f121,f131,f137,f155,f183,f197,f228,f241,f260,f264])).

fof(f264,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f263,f238,f133,f90,f83,f68,f58])).

fof(f58,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f83,plain,
    ( spl3_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f90,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f133,plain,
    ( spl3_15
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f238,plain,
    ( spl3_28
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f263,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f261,f135])).

fof(f135,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f261,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f91,f85,f70,f240,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1)))
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f38,f37,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1)))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (17896)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f240,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f238])).

fof(f70,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f85,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f91,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f260,plain,
    ( ~ spl3_28
    | spl3_2
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f258,f226,f54,f238])).

fof(f54,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f226,plain,
    ( spl3_26
  <=> ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f258,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_2
    | ~ spl3_26 ),
    inference(resolution,[],[f227,f56])).

fof(f56,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

% (17887)Refutation not found, incomplete strategy% (17887)------------------------------
% (17887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17887)Termination reason: Refutation not found, incomplete strategy

% (17887)Memory used [KB]: 10618
% (17887)Time elapsed: 0.121 s
% (17887)------------------------------
% (17887)------------------------------
fof(f227,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f241,plain,
    ( spl3_28
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f236,f193,f238])).

fof(f193,plain,
    ( spl3_22
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f236,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f195,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

% (17905)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f195,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f193])).

fof(f228,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_26
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f224,f126,f118,f68,f226,f83,f90])).

fof(f118,plain,
    ( spl3_13
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f126,plain,
    ( spl3_14
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f224,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f223,f128])).

fof(f128,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f222,f120])).

fof(f120,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
        | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5 ),
    inference(resolution,[],[f157,f70])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f38,f37,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f197,plain,
    ( ~ spl3_6
    | spl3_22
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f190,f180,f193,f73])).

fof(f73,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f180,plain,
    ( spl3_21
  <=> k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f190,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_21 ),
    inference(superposition,[],[f43,f182])).

fof(f182,plain,
    ( k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f183,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f178,f152,f73,f180])).

fof(f152,plain,
    ( spl3_18
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f178,plain,
    ( k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f175,f154])).

fof(f154,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f175,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f155,plain,
    ( spl3_18
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f150,f73,f152])).

fof(f150,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f75,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f137,plain,
    ( spl3_15
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f136,f126,f112,f133])).

fof(f112,plain,
    ( spl3_12
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f136,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f114,f128])).

fof(f114,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f131,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f130,f73,f63,f126])).

fof(f63,plain,
    ( spl3_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f130,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f123,f65])).

fof(f65,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f123,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f41,f75])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f121,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f116,f90,f83,f68,f118])).

fof(f116,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f91,f85,f70,f36])).

fof(f115,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f110,f90,f83,f68,f112])).

fof(f110,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f91,f85,f70,f35])).

fof(f102,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f101,f73,f90])).

fof(f101,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f94,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f88,f50,f83,f90])).

fof(f50,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f38,f52])).

fof(f52,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f86,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f83])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

% (17904)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f76,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f58,f54,f50])).

fof(f34,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (17886)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  % (17889)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.53  % (17907)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (17902)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  % (17890)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.54  % (17899)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.54  % (17892)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.54  % (17884)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.54  % (17887)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.54  % (17888)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.54  % (17890)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (17885)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.54  % (17907)Refutation not found, incomplete strategy% (17907)------------------------------
% 0.22/0.54  % (17907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17907)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17907)Memory used [KB]: 10618
% 0.22/0.54  % (17907)Time elapsed: 0.070 s
% 0.22/0.54  % (17907)------------------------------
% 0.22/0.54  % (17907)------------------------------
% 0.22/0.54  % (17892)Refutation not found, incomplete strategy% (17892)------------------------------
% 0.22/0.54  % (17892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17892)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17892)Memory used [KB]: 10618
% 0.22/0.54  % (17892)Time elapsed: 0.070 s
% 0.22/0.54  % (17892)------------------------------
% 0.22/0.54  % (17892)------------------------------
% 0.22/0.54  % (17901)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.54  % (17895)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.54  % (17898)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f86,f94,f102,f115,f121,f131,f137,f155,f183,f197,f228,f241,f260,f264])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_15 | ~spl3_28),
% 0.22/0.54    inference(avatar_split_clause,[],[f263,f238,f133,f90,f83,f68,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    spl3_5 <=> v2_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    spl3_8 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    spl3_9 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    spl3_15 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    spl3_28 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_15 | ~spl3_28)),
% 0.22/0.54    inference(forward_demodulation,[],[f261,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f133])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_28)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f91,f85,f70,f240,f162])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_funct_1(X0) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1))) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(global_subsumption,[],[f38,f37,f161])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(superposition,[],[f48,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  % (17896)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f240,plain,(
% 0.22/0.55    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_28),
% 0.22/0.55    inference(avatar_component_clause,[],[f238])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    v2_funct_1(sK2) | ~spl3_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    v1_funct_1(sK2) | ~spl3_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f83])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    v1_relat_1(sK2) | ~spl3_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f90])).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    ~spl3_28 | spl3_2 | ~spl3_26),
% 0.22/0.55    inference(avatar_split_clause,[],[f258,f226,f54,f238])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.55  fof(f226,plain,(
% 0.22/0.55    spl3_26 <=> ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl3_2 | ~spl3_26)),
% 0.22/0.55    inference(resolution,[],[f227,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f54])).
% 0.22/0.55  % (17887)Refutation not found, incomplete strategy% (17887)------------------------------
% 0.22/0.55  % (17887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17887)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17887)Memory used [KB]: 10618
% 0.22/0.55  % (17887)Time elapsed: 0.121 s
% 0.22/0.55  % (17887)------------------------------
% 0.22/0.55  % (17887)------------------------------
% 0.22/0.55  fof(f227,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_26),
% 0.22/0.55    inference(avatar_component_clause,[],[f226])).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    spl3_28 | ~spl3_22),
% 0.22/0.55    inference(avatar_split_clause,[],[f236,f193,f238])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    spl3_22 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.55  fof(f236,plain,(
% 0.22/0.55    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_22),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f195,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  % (17905)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f193])).
% 0.22/0.55  fof(f228,plain,(
% 0.22/0.55    ~spl3_9 | ~spl3_8 | spl3_26 | ~spl3_5 | ~spl3_13 | ~spl3_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f224,f126,f118,f68,f226,f83,f90])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    spl3_13 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    spl3_14 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl3_5 | ~spl3_13 | ~spl3_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f223,f128])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    sK1 = k2_relat_1(sK2) | ~spl3_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f126])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl3_5 | ~spl3_13)),
% 0.22/0.55    inference(forward_demodulation,[],[f222,f120])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f118])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_5),
% 0.22/0.55    inference(resolution,[],[f157,f70])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v2_funct_1(X0) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(global_subsumption,[],[f38,f37,f156])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),X1) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(superposition,[],[f47,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    ~spl3_6 | spl3_22 | ~spl3_21),
% 0.22/0.55    inference(avatar_split_clause,[],[f190,f180,f193,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    spl3_21 <=> k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.55  fof(f190,plain,(
% 0.22/0.55    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_21),
% 0.22/0.55    inference(superposition,[],[f43,f182])).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl3_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f180])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    spl3_21 | ~spl3_6 | ~spl3_18),
% 0.22/0.55    inference(avatar_split_clause,[],[f178,f152,f73,f180])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    spl3_18 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl3_6 | ~spl3_18)),
% 0.22/0.55    inference(forward_demodulation,[],[f175,f154])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_18),
% 0.22/0.55    inference(avatar_component_clause,[],[f152])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl3_6),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f75,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f73])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    spl3_18 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f150,f73,f152])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_6),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f75,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl3_15 | ~spl3_12 | ~spl3_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f136,f126,f112,f133])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    spl3_12 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_14)),
% 0.22/0.55    inference(backward_demodulation,[],[f114,f128])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f112])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    spl3_14 | ~spl3_4 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f130,f73,f63,f126])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    spl3_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_6)),
% 0.22/0.55    inference(forward_demodulation,[],[f123,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f63])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_6),
% 0.22/0.55    inference(resolution,[],[f41,f75])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    spl3_13 | ~spl3_5 | ~spl3_8 | ~spl3_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f116,f90,f83,f68,f118])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_9)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f91,f85,f70,f36])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    spl3_12 | ~spl3_5 | ~spl3_8 | ~spl3_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f110,f90,f83,f68,f112])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_9)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f91,f85,f70,f35])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    spl3_9 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f101,f73,f90])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    v1_relat_1(sK2) | ~spl3_6),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f75,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ~spl3_9 | ~spl3_8 | spl3_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f88,f50,f83,f90])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.55    inference(resolution,[],[f38,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f50])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    spl3_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f29,f83])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f10])).
% 0.22/0.55  % (17904)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.55  fof(f10,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f31,f73])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    spl3_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f32,f68])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    v2_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f33,f63])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f34,f58,f54,f50])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (17890)------------------------------
% 0.22/0.55  % (17890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17890)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (17890)Memory used [KB]: 10874
% 0.22/0.55  % (17890)Time elapsed: 0.125 s
% 0.22/0.55  % (17890)------------------------------
% 0.22/0.55  % (17890)------------------------------
% 0.22/0.55  % (17883)Success in time 0.187 s
%------------------------------------------------------------------------------

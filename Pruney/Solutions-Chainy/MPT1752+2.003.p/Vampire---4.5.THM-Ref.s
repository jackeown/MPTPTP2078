%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:25 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 368 expanded)
%              Number of leaves         :   44 ( 176 expanded)
%              Depth                    :    8
%              Number of atoms          :  548 (2448 expanded)
%              Number of equality atoms :   52 ( 229 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31838)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f815,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f86,f91,f96,f101,f111,f116,f121,f126,f131,f136,f148,f157,f197,f203,f214,f222,f230,f237,f275,f343,f755,f760,f779,f814])).

fof(f814,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,u1_struct_0(sK2))
    | k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | k10_relat_1(sK3,sK4) = k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f779,plain,
    ( ~ spl5_4
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | ~ spl5_4
    | spl5_33 ),
    inference(unit_resulting_resolution,[],[f85,f270,f151])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X3)),X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f66,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f270,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl5_33
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f85,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f760,plain,
    ( ~ spl5_16
    | ~ spl5_17
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | ~ spl5_16
    | ~ spl5_17
    | spl5_32 ),
    inference(unit_resulting_resolution,[],[f456,f266,f66])).

fof(f266,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl5_32
  <=> v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f456,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f250,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f250,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f171,f147,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f147,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_16
  <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f171,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f156,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f755,plain,
    ( ~ spl5_16
    | ~ spl5_17
    | spl5_40 ),
    inference(avatar_contradiction_clause,[],[f753])).

fof(f753,plain,
    ( $false
    | ~ spl5_16
    | ~ spl5_17
    | spl5_40 ),
    inference(unit_resulting_resolution,[],[f326,f456,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f65,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f326,plain,
    ( ~ m1_subset_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_40 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl5_40
  <=> m1_subset_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f343,plain,
    ( ~ spl5_40
    | spl5_34 ),
    inference(avatar_split_clause,[],[f322,f272,f324])).

fof(f272,plain,
    ( spl5_34
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f322,plain,
    ( ~ m1_subset_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_34 ),
    inference(resolution,[],[f274,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f274,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))
    | spl5_34 ),
    inference(avatar_component_clause,[],[f272])).

fof(f275,plain,
    ( ~ spl5_32
    | ~ spl5_33
    | ~ spl5_34
    | spl5_28 ),
    inference(avatar_split_clause,[],[f256,f234,f272,f268,f264])).

fof(f234,plain,
    ( spl5_28
  <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f256,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | spl5_28 ),
    inference(resolution,[],[f236,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f236,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f234])).

fof(f237,plain,
    ( ~ spl5_28
    | spl5_24
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f231,f227,f207,f234])).

fof(f207,plain,
    ( spl5_24
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f227,plain,
    ( spl5_27
  <=> k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f231,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_24
    | ~ spl5_27 ),
    inference(backward_demodulation,[],[f209,f229])).

fof(f229,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f227])).

fof(f209,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f207])).

fof(f230,plain,
    ( spl5_27
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f225,f133,f128,f123,f118,f113,f108,f98,f93,f88,f83,f227])).

fof(f88,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f93,plain,
    ( spl5_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f98,plain,
    ( spl5_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f108,plain,
    ( spl5_9
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f113,plain,
    ( spl5_10
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f118,plain,
    ( spl5_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f123,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f128,plain,
    ( spl5_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f133,plain,
    ( spl5_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f225,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(forward_demodulation,[],[f223,f216])).

fof(f216,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f95,f85,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f95,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f223,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f135,f130,f125,f120,f115,f110,f95,f100,f90,f85,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f90,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f100,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f110,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f115,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f120,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f222,plain,
    ( spl5_26
    | ~ spl5_6
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f217,f199,f154,f93,f219])).

fof(f219,plain,
    ( spl5_26
  <=> k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f199,plain,
    ( spl5_23
  <=> r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f217,plain,
    ( k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ spl5_6
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f156,f95,f201,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f201,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f214,plain,
    ( ~ spl5_24
    | ~ spl5_25
    | spl5_22 ),
    inference(avatar_split_clause,[],[f205,f194,f211,f207])).

fof(f211,plain,
    ( spl5_25
  <=> k10_relat_1(sK3,sK4) = k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f194,plain,
    ( spl5_22
  <=> k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) = k10_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f205,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_22 ),
    inference(superposition,[],[f196,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f196,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f203,plain,
    ( ~ spl5_4
    | spl5_23
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f184,f73,f199,f83])).

fof(f73,plain,
    ( spl5_2
  <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f184,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_2 ),
    inference(superposition,[],[f75,f55])).

fof(f75,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f197,plain,
    ( ~ spl5_22
    | spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f186,f83,f68,f194])).

fof(f68,plain,
    ( spl5_1
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f186,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4)
    | spl5_1
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f70,f183])).

fof(f183,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f85,f55])).

fof(f70,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f157,plain,
    ( spl5_17
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f150,f83,f154])).

fof(f150,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f85,f66])).

fof(f148,plain,
    ( spl5_16
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f143,f83,f145])).

fof(f143,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f85,f61])).

fof(f136,plain,(
    ~ spl5_14 ),
    inference(avatar_split_clause,[],[f40,f133])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4)
                  & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4)
                & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4)
              & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4)
            & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4)
        & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2))
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                       => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tmap_1)).

fof(f131,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f41,f128])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f126,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f42,f123])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f43,f118])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f44,f113])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f45,f108])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f50,f83])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f52,f73])).

fof(f52,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f53,f68])).

fof(f53,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:35:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (31842)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (31840)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (31850)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (31837)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (31845)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (31858)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (31848)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.30/0.52  % (31842)Refutation found. Thanks to Tanya!
% 1.30/0.52  % SZS status Theorem for theBenchmark
% 1.30/0.52  % SZS output start Proof for theBenchmark
% 1.30/0.54  % (31838)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.45/0.54  fof(f815,plain,(
% 1.45/0.54    $false),
% 1.45/0.54    inference(avatar_sat_refutation,[],[f71,f76,f86,f91,f96,f101,f111,f116,f121,f126,f131,f136,f148,f157,f197,f203,f214,f222,f230,f237,f275,f343,f755,f760,f779,f814])).
% 1.45/0.54  fof(f814,plain,(
% 1.45/0.54    k2_tmap_1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,u1_struct_0(sK2)) | k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | k10_relat_1(sK3,sK4) = k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 1.45/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.45/0.54  fof(f779,plain,(
% 1.45/0.54    ~spl5_4 | spl5_33),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f763])).
% 1.45/0.54  fof(f763,plain,(
% 1.45/0.54    $false | (~spl5_4 | spl5_33)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f85,f270,f151])).
% 1.45/0.54  fof(f151,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X0,X3)),X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.45/0.54    inference(resolution,[],[f66,f63])).
% 1.45/0.54  fof(f63,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f29])).
% 1.45/0.54  fof(f29,plain,(
% 1.45/0.54    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f3])).
% 1.45/0.54  fof(f3,axiom,(
% 1.45/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.45/0.54  fof(f66,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.54    inference(cnf_transformation,[],[f32])).
% 1.45/0.54  fof(f32,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.54    inference(ennf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.45/0.54  fof(f270,plain,(
% 1.45/0.54    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | spl5_33),
% 1.45/0.54    inference(avatar_component_clause,[],[f268])).
% 1.45/0.54  fof(f268,plain,(
% 1.45/0.54    spl5_33 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.45/0.54  fof(f85,plain,(
% 1.45/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_4),
% 1.45/0.54    inference(avatar_component_clause,[],[f83])).
% 1.45/0.54  fof(f83,plain,(
% 1.45/0.54    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.45/0.55  fof(f760,plain,(
% 1.45/0.55    ~spl5_16 | ~spl5_17 | spl5_32),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f758])).
% 1.45/0.55  fof(f758,plain,(
% 1.45/0.55    $false | (~spl5_16 | ~spl5_17 | spl5_32)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f456,f266,f66])).
% 1.45/0.55  fof(f266,plain,(
% 1.45/0.55    ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | spl5_32),
% 1.45/0.55    inference(avatar_component_clause,[],[f264])).
% 1.45/0.55  fof(f264,plain,(
% 1.45/0.55    spl5_32 <=> v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.45/0.55  fof(f456,plain,(
% 1.45/0.55    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) ) | (~spl5_16 | ~spl5_17)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f250,f62])).
% 1.45/0.55  fof(f62,plain,(
% 1.45/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f39])).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.45/0.55    inference(nnf_transformation,[],[f2])).
% 1.45/0.55  fof(f2,axiom,(
% 1.45/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.45/0.55  fof(f250,plain,(
% 1.45/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) | (~spl5_16 | ~spl5_17)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f171,f147,f59])).
% 1.45/0.55  fof(f59,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f26])).
% 1.45/0.55  fof(f26,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.45/0.55    inference(flattening,[],[f25])).
% 1.45/0.55  fof(f25,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.45/0.55    inference(ennf_transformation,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.45/0.55  fof(f147,plain,(
% 1.45/0.55    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl5_16),
% 1.45/0.55    inference(avatar_component_clause,[],[f145])).
% 1.45/0.55  fof(f145,plain,(
% 1.45/0.55    spl5_16 <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.45/0.55  fof(f171,plain,(
% 1.45/0.55    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) ) | ~spl5_17),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f156,f64])).
% 1.45/0.55  fof(f64,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f30])).
% 1.45/0.55  fof(f30,plain,(
% 1.45/0.55    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.45/0.55    inference(ennf_transformation,[],[f4])).
% 1.45/0.55  fof(f4,axiom,(
% 1.45/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.45/0.55  fof(f156,plain,(
% 1.45/0.55    v1_relat_1(sK3) | ~spl5_17),
% 1.45/0.55    inference(avatar_component_clause,[],[f154])).
% 1.45/0.55  fof(f154,plain,(
% 1.45/0.55    spl5_17 <=> v1_relat_1(sK3)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.45/0.55  fof(f755,plain,(
% 1.45/0.55    ~spl5_16 | ~spl5_17 | spl5_40),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f753])).
% 1.45/0.55  fof(f753,plain,(
% 1.45/0.55    $false | (~spl5_16 | ~spl5_17 | spl5_40)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f326,f456,f176])).
% 1.45/0.55  fof(f176,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f175])).
% 1.45/0.55  fof(f175,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.55    inference(superposition,[],[f65,f56])).
% 1.45/0.55  fof(f56,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f20])).
% 1.45/0.55  fof(f20,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.55    inference(ennf_transformation,[],[f7])).
% 1.45/0.55  fof(f7,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.45/0.55  fof(f65,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f31])).
% 1.45/0.55  fof(f31,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.55    inference(ennf_transformation,[],[f6])).
% 1.45/0.55  fof(f6,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.45/0.55  fof(f326,plain,(
% 1.45/0.55    ~m1_subset_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_40),
% 1.45/0.55    inference(avatar_component_clause,[],[f324])).
% 1.45/0.55  fof(f324,plain,(
% 1.45/0.55    spl5_40 <=> m1_subset_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.45/0.55  fof(f343,plain,(
% 1.45/0.55    ~spl5_40 | spl5_34),
% 1.45/0.55    inference(avatar_split_clause,[],[f322,f272,f324])).
% 1.45/0.55  fof(f272,plain,(
% 1.45/0.55    spl5_34 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.45/0.55  fof(f322,plain,(
% 1.45/0.55    ~m1_subset_1(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_34),
% 1.45/0.55    inference(resolution,[],[f274,f61])).
% 1.45/0.55  fof(f61,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f39])).
% 1.45/0.55  fof(f274,plain,(
% 1.45/0.55    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) | spl5_34),
% 1.45/0.55    inference(avatar_component_clause,[],[f272])).
% 1.45/0.55  fof(f275,plain,(
% 1.45/0.55    ~spl5_32 | ~spl5_33 | ~spl5_34 | spl5_28),
% 1.45/0.55    inference(avatar_split_clause,[],[f256,f234,f272,f268,f264])).
% 1.45/0.55  fof(f234,plain,(
% 1.45/0.55    spl5_28 <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.45/0.55  fof(f256,plain,(
% 1.45/0.55    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) | ~v1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | spl5_28),
% 1.45/0.55    inference(resolution,[],[f236,f60])).
% 1.45/0.55  fof(f60,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f28])).
% 1.45/0.55  fof(f28,plain,(
% 1.45/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.45/0.55    inference(flattening,[],[f27])).
% 1.45/0.55  fof(f27,plain,(
% 1.45/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.45/0.55    inference(ennf_transformation,[],[f9])).
% 1.45/0.55  fof(f9,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.45/0.55  fof(f236,plain,(
% 1.45/0.55    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl5_28),
% 1.45/0.55    inference(avatar_component_clause,[],[f234])).
% 1.45/0.55  fof(f237,plain,(
% 1.45/0.55    ~spl5_28 | spl5_24 | ~spl5_27),
% 1.45/0.55    inference(avatar_split_clause,[],[f231,f227,f207,f234])).
% 1.45/0.55  fof(f207,plain,(
% 1.45/0.55    spl5_24 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.45/0.55  fof(f227,plain,(
% 1.45/0.55    spl5_27 <=> k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.45/0.55  fof(f231,plain,(
% 1.45/0.55    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | (spl5_24 | ~spl5_27)),
% 1.45/0.55    inference(backward_demodulation,[],[f209,f229])).
% 1.45/0.55  fof(f229,plain,(
% 1.45/0.55    k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | ~spl5_27),
% 1.45/0.55    inference(avatar_component_clause,[],[f227])).
% 1.45/0.55  fof(f209,plain,(
% 1.45/0.55    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl5_24),
% 1.45/0.55    inference(avatar_component_clause,[],[f207])).
% 1.45/0.55  fof(f230,plain,(
% 1.45/0.55    spl5_27 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | spl5_14),
% 1.45/0.55    inference(avatar_split_clause,[],[f225,f133,f128,f123,f118,f113,f108,f98,f93,f88,f83,f227])).
% 1.45/0.55  fof(f88,plain,(
% 1.45/0.55    spl5_5 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.45/0.55  fof(f93,plain,(
% 1.45/0.55    spl5_6 <=> v1_funct_1(sK3)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.45/0.55  fof(f98,plain,(
% 1.45/0.55    spl5_7 <=> m1_pre_topc(sK2,sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.45/0.55  fof(f108,plain,(
% 1.45/0.55    spl5_9 <=> l1_pre_topc(sK1)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.45/0.55  fof(f113,plain,(
% 1.45/0.55    spl5_10 <=> v2_pre_topc(sK1)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.45/0.55  fof(f118,plain,(
% 1.45/0.55    spl5_11 <=> v2_struct_0(sK1)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.45/0.55  fof(f123,plain,(
% 1.45/0.55    spl5_12 <=> l1_pre_topc(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.45/0.55  fof(f128,plain,(
% 1.45/0.55    spl5_13 <=> v2_pre_topc(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.45/0.55  fof(f133,plain,(
% 1.45/0.55    spl5_14 <=> v2_struct_0(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.45/0.55  fof(f225,plain,(
% 1.45/0.55    k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | spl5_14)),
% 1.45/0.55    inference(forward_demodulation,[],[f223,f216])).
% 1.45/0.55  fof(f216,plain,(
% 1.45/0.55    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0)) ) | (~spl5_4 | ~spl5_6)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f95,f85,f54])).
% 1.45/0.55  fof(f54,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f18])).
% 1.45/0.55  fof(f18,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.45/0.55    inference(flattening,[],[f17])).
% 1.45/0.55  fof(f17,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.45/0.55    inference(ennf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.45/0.55  fof(f95,plain,(
% 1.45/0.55    v1_funct_1(sK3) | ~spl5_6),
% 1.45/0.55    inference(avatar_component_clause,[],[f93])).
% 1.45/0.55  fof(f223,plain,(
% 1.45/0.55    k2_tmap_1(sK0,sK1,sK3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | spl5_14)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f135,f130,f125,f120,f115,f110,f95,f100,f90,f85,f58])).
% 1.45/0.55  fof(f58,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.55    inference(flattening,[],[f23])).
% 1.45/0.55  fof(f23,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f12])).
% 1.45/0.55  fof(f12,axiom,(
% 1.45/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.45/0.55  fof(f90,plain,(
% 1.45/0.55    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_5),
% 1.45/0.55    inference(avatar_component_clause,[],[f88])).
% 1.45/0.55  fof(f100,plain,(
% 1.45/0.55    m1_pre_topc(sK2,sK0) | ~spl5_7),
% 1.45/0.55    inference(avatar_component_clause,[],[f98])).
% 1.45/0.55  fof(f110,plain,(
% 1.45/0.55    l1_pre_topc(sK1) | ~spl5_9),
% 1.45/0.55    inference(avatar_component_clause,[],[f108])).
% 1.45/0.55  fof(f115,plain,(
% 1.45/0.55    v2_pre_topc(sK1) | ~spl5_10),
% 1.45/0.55    inference(avatar_component_clause,[],[f113])).
% 1.45/0.55  fof(f120,plain,(
% 1.45/0.55    ~v2_struct_0(sK1) | spl5_11),
% 1.45/0.55    inference(avatar_component_clause,[],[f118])).
% 1.45/0.55  fof(f125,plain,(
% 1.45/0.55    l1_pre_topc(sK0) | ~spl5_12),
% 1.45/0.55    inference(avatar_component_clause,[],[f123])).
% 1.45/0.55  fof(f130,plain,(
% 1.45/0.55    v2_pre_topc(sK0) | ~spl5_13),
% 1.45/0.55    inference(avatar_component_clause,[],[f128])).
% 1.45/0.55  fof(f135,plain,(
% 1.45/0.55    ~v2_struct_0(sK0) | spl5_14),
% 1.45/0.55    inference(avatar_component_clause,[],[f133])).
% 1.45/0.55  fof(f222,plain,(
% 1.45/0.55    spl5_26 | ~spl5_6 | ~spl5_17 | ~spl5_23),
% 1.45/0.55    inference(avatar_split_clause,[],[f217,f199,f154,f93,f219])).
% 1.45/0.55  fof(f219,plain,(
% 1.45/0.55    spl5_26 <=> k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.45/0.55  fof(f199,plain,(
% 1.45/0.55    spl5_23 <=> r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.45/0.55  fof(f217,plain,(
% 1.45/0.55    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | (~spl5_6 | ~spl5_17 | ~spl5_23)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f156,f95,f201,f57])).
% 1.45/0.55  fof(f57,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f22])).
% 1.45/0.55  fof(f22,plain,(
% 1.45/0.55    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.55    inference(flattening,[],[f21])).
% 1.45/0.55  fof(f21,plain,(
% 1.45/0.55    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f11])).
% 1.45/0.55  fof(f11,axiom,(
% 1.45/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.45/0.55  fof(f201,plain,(
% 1.45/0.55    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) | ~spl5_23),
% 1.45/0.55    inference(avatar_component_clause,[],[f199])).
% 1.45/0.55  fof(f214,plain,(
% 1.45/0.55    ~spl5_24 | ~spl5_25 | spl5_22),
% 1.45/0.55    inference(avatar_split_clause,[],[f205,f194,f211,f207])).
% 1.45/0.55  fof(f211,plain,(
% 1.45/0.55    spl5_25 <=> k10_relat_1(sK3,sK4) = k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.45/0.55  fof(f194,plain,(
% 1.45/0.55    spl5_22 <=> k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) = k10_relat_1(sK3,sK4)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.45/0.55  fof(f205,plain,(
% 1.45/0.55    k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl5_22),
% 1.45/0.55    inference(superposition,[],[f196,f55])).
% 1.45/0.55  fof(f55,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f19])).
% 1.45/0.55  fof(f19,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.55    inference(ennf_transformation,[],[f8])).
% 1.45/0.55  fof(f8,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.45/0.55  fof(f196,plain,(
% 1.45/0.55    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4) | spl5_22),
% 1.45/0.55    inference(avatar_component_clause,[],[f194])).
% 1.45/0.55  fof(f203,plain,(
% 1.45/0.55    ~spl5_4 | spl5_23 | ~spl5_2),
% 1.45/0.55    inference(avatar_split_clause,[],[f184,f73,f199,f83])).
% 1.45/0.55  fof(f73,plain,(
% 1.45/0.55    spl5_2 <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.45/0.55  fof(f184,plain,(
% 1.45/0.55    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_2),
% 1.45/0.55    inference(superposition,[],[f75,f55])).
% 1.45/0.55  fof(f75,plain,(
% 1.45/0.55    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) | ~spl5_2),
% 1.45/0.55    inference(avatar_component_clause,[],[f73])).
% 1.45/0.55  fof(f197,plain,(
% 1.45/0.55    ~spl5_22 | spl5_1 | ~spl5_4),
% 1.45/0.55    inference(avatar_split_clause,[],[f186,f83,f68,f194])).
% 1.45/0.55  fof(f68,plain,(
% 1.45/0.55    spl5_1 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.45/0.55  fof(f186,plain,(
% 1.45/0.55    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4) | (spl5_1 | ~spl5_4)),
% 1.45/0.55    inference(backward_demodulation,[],[f70,f183])).
% 1.45/0.55  fof(f183,plain,(
% 1.45/0.55    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl5_4),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f85,f55])).
% 1.45/0.55  fof(f70,plain,(
% 1.45/0.55    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) | spl5_1),
% 1.45/0.55    inference(avatar_component_clause,[],[f68])).
% 1.45/0.55  fof(f157,plain,(
% 1.45/0.55    spl5_17 | ~spl5_4),
% 1.45/0.55    inference(avatar_split_clause,[],[f150,f83,f154])).
% 1.45/0.55  fof(f150,plain,(
% 1.45/0.55    v1_relat_1(sK3) | ~spl5_4),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f85,f66])).
% 1.45/0.55  fof(f148,plain,(
% 1.45/0.55    spl5_16 | ~spl5_4),
% 1.45/0.55    inference(avatar_split_clause,[],[f143,f83,f145])).
% 1.45/0.55  fof(f143,plain,(
% 1.45/0.55    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl5_4),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f85,f61])).
% 1.45/0.55  fof(f136,plain,(
% 1.45/0.55    ~spl5_14),
% 1.45/0.55    inference(avatar_split_clause,[],[f40,f133])).
% 1.45/0.55  fof(f40,plain,(
% 1.45/0.55    ~v2_struct_0(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.45/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f37,f36,f35,f34,f33])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f34,plain,(
% 1.45/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f35,plain,(
% 1.45/0.55    ? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f36,plain,(
% 1.45/0.55    ? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f37,plain,(
% 1.45/0.55    ? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.45/0.55    introduced(choice_axiom,[])).
% 1.45/0.55  fof(f16,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/0.55    inference(flattening,[],[f15])).
% 1.45/0.55  fof(f15,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f14])).
% 1.45/0.55  fof(f14,negated_conjecture,(
% 1.45/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 1.45/0.55    inference(negated_conjecture,[],[f13])).
% 1.45/0.55  fof(f13,conjecture,(
% 1.45/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tmap_1)).
% 1.45/0.55  fof(f131,plain,(
% 1.45/0.55    spl5_13),
% 1.45/0.55    inference(avatar_split_clause,[],[f41,f128])).
% 1.45/0.55  fof(f41,plain,(
% 1.45/0.55    v2_pre_topc(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f126,plain,(
% 1.45/0.55    spl5_12),
% 1.45/0.55    inference(avatar_split_clause,[],[f42,f123])).
% 1.45/0.55  fof(f42,plain,(
% 1.45/0.55    l1_pre_topc(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f121,plain,(
% 1.45/0.55    ~spl5_11),
% 1.45/0.55    inference(avatar_split_clause,[],[f43,f118])).
% 1.45/0.55  fof(f43,plain,(
% 1.45/0.55    ~v2_struct_0(sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f116,plain,(
% 1.45/0.55    spl5_10),
% 1.45/0.55    inference(avatar_split_clause,[],[f44,f113])).
% 1.45/0.55  fof(f44,plain,(
% 1.45/0.55    v2_pre_topc(sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f111,plain,(
% 1.45/0.55    spl5_9),
% 1.45/0.55    inference(avatar_split_clause,[],[f45,f108])).
% 1.45/0.55  fof(f45,plain,(
% 1.45/0.55    l1_pre_topc(sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f101,plain,(
% 1.45/0.55    spl5_7),
% 1.45/0.55    inference(avatar_split_clause,[],[f47,f98])).
% 1.45/0.55  fof(f47,plain,(
% 1.45/0.55    m1_pre_topc(sK2,sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f96,plain,(
% 1.45/0.55    spl5_6),
% 1.45/0.55    inference(avatar_split_clause,[],[f48,f93])).
% 1.45/0.55  fof(f48,plain,(
% 1.45/0.55    v1_funct_1(sK3)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f91,plain,(
% 1.45/0.55    spl5_5),
% 1.45/0.55    inference(avatar_split_clause,[],[f49,f88])).
% 1.45/0.55  fof(f49,plain,(
% 1.45/0.55    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f86,plain,(
% 1.45/0.55    spl5_4),
% 1.45/0.55    inference(avatar_split_clause,[],[f50,f83])).
% 1.45/0.55  fof(f50,plain,(
% 1.45/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f76,plain,(
% 1.45/0.55    spl5_2),
% 1.45/0.55    inference(avatar_split_clause,[],[f52,f73])).
% 1.45/0.55  fof(f52,plain,(
% 1.45/0.55    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f71,plain,(
% 1.45/0.55    ~spl5_1),
% 1.45/0.55    inference(avatar_split_clause,[],[f53,f68])).
% 1.45/0.55  fof(f53,plain,(
% 1.45/0.55    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (31842)------------------------------
% 1.45/0.55  % (31842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (31842)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (31842)Memory used [KB]: 11385
% 1.45/0.55  % (31842)Time elapsed: 0.127 s
% 1.45/0.55  % (31842)------------------------------
% 1.45/0.55  % (31842)------------------------------
% 1.45/0.55  % (31835)Success in time 0.187 s
%------------------------------------------------------------------------------

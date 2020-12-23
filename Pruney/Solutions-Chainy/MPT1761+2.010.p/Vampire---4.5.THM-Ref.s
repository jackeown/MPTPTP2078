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
% DateTime   : Thu Dec  3 13:18:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 361 expanded)
%              Number of leaves         :   39 ( 199 expanded)
%              Depth                    :    7
%              Number of atoms          :  556 (3783 expanded)
%              Number of equality atoms :   47 ( 309 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f119,f124,f129,f134,f139,f144,f169,f186,f194,f202,f208,f218,f226,f239])).

fof(f239,plain,
    ( spl6_9
    | ~ spl6_25
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f237,f211,f191,f101])).

fof(f101,plain,
    ( spl6_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f191,plain,
    ( spl6_25
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f211,plain,
    ( spl6_28
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f237,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl6_28 ),
    inference(resolution,[],[f213,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

% (26353)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f213,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f211])).

fof(f226,plain,
    ( spl6_29
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f225,f183,f91,f66,f215])).

fof(f215,plain,
    ( spl6_29
  <=> k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f66,plain,
    ( spl6_2
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f91,plain,
    ( spl6_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f183,plain,
    ( spl6_24
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f225,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f68,f93,f185,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

% (26365)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f185,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f183])).

fof(f93,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f91])).

% (26376)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f68,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f218,plain,
    ( spl6_28
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_3
    | ~ spl6_29
    | spl6_27 ),
    inference(avatar_split_clause,[],[f209,f205,f215,f71,f81,f86,f91,f211])).

% (26355)Refutation not found, incomplete strategy% (26355)------------------------------
% (26355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26355)Termination reason: Refutation not found, incomplete strategy

% (26355)Memory used [KB]: 10618
% (26355)Time elapsed: 0.089 s
% (26355)------------------------------
% (26355)------------------------------
fof(f86,plain,
    ( spl6_6
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f81,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f71,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f205,plain,
    ( spl6_27
  <=> k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f209,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK3))
    | spl6_27 ),
    inference(superposition,[],[f207,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f207,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f205])).

fof(f208,plain,
    ( ~ spl6_27
    | spl6_1
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f203,f199,f61,f205])).

fof(f61,plain,
    ( spl6_1
  <=> k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f199,plain,
    ( spl6_26
  <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f203,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | spl6_1
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f63,f201])).

fof(f201,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f63,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f202,plain,
    ( spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(avatar_split_clause,[],[f197,f141,f136,f131,f126,f121,f116,f106,f96,f91,f86,f81,f76,f199])).

fof(f76,plain,
    ( spl6_4
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f96,plain,
    ( spl6_8
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f106,plain,
    ( spl6_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f116,plain,
    ( spl6_12
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f121,plain,
    ( spl6_13
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f126,plain,
    ( spl6_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f131,plain,
    ( spl6_15
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f136,plain,
    ( spl6_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f141,plain,
    ( spl6_17
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f197,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(forward_demodulation,[],[f195,f187])).

fof(f187,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f93,f83,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f83,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f195,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f143,f138,f133,f128,f123,f118,f98,f108,f93,f78,f88,f83,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f88,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f78,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f108,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f106])).

% (26368)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f98,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f118,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f128,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f133,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f138,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f143,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f194,plain,
    ( spl6_25
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f189,f166,f191])).

fof(f166,plain,
    ( spl6_21
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f189,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f168,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (26361)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f168,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f166])).

fof(f186,plain,
    ( spl6_24
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f181,f81,f183])).

fof(f181,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f56,f83,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f169,plain,
    ( spl6_21
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f164,f131,f96,f166])).

fof(f164,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f133,f98,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f144,plain,(
    ~ spl6_17 ),
    inference(avatar_split_clause,[],[f34,f141])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & r2_hidden(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f32,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r2_hidden(X5,u1_struct_0(X2))
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
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
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                        & r2_hidden(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                      & r2_hidden(X5,u1_struct_0(X2))
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                    & r2_hidden(X5,u1_struct_0(X2))
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                  & r2_hidden(X5,u1_struct_0(sK2))
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                & r2_hidden(X5,u1_struct_0(sK2))
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
              & r2_hidden(X5,u1_struct_0(sK2))
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
            & r2_hidden(X5,u1_struct_0(sK2))
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
          & r2_hidden(X5,u1_struct_0(sK2))
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X5] :
        ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
        & r2_hidden(X5,u1_struct_0(sK2))
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
      & r2_hidden(sK5,u1_struct_0(sK2))
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

fof(f139,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f35,f136])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f134,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f36,f131])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f37,f126])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f38,f121])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f39,f116])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f41,f106])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f42,f101])).

fof(f42,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f45,f86])).

fof(f45,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f47,f76])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f48,f71])).

fof(f48,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f49,f66])).

fof(f49,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f50,f61])).

fof(f50,plain,(
    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (26358)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (26358)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (26356)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (26375)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (26357)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.51  % (26355)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (26352)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (26367)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f119,f124,f129,f134,f139,f144,f169,f186,f194,f202,f208,f218,f226,f239])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    spl6_9 | ~spl6_25 | ~spl6_28),
% 0.20/0.51    inference(avatar_split_clause,[],[f237,f211,f191,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl6_9 <=> v2_struct_0(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    spl6_25 <=> l1_struct_0(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    spl6_28 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl6_28),
% 0.20/0.51    inference(resolution,[],[f213,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  % (26353)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~spl6_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f211])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    spl6_29 | ~spl6_2 | ~spl6_7 | ~spl6_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f225,f183,f91,f66,f215])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    spl6_29 <=> k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl6_2 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl6_7 <=> v1_funct_1(sK4)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    spl6_24 <=> v1_relat_1(sK4)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) | (~spl6_2 | ~spl6_7 | ~spl6_24)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f68,f93,f185,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  % (26365)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    v1_relat_1(sK4) | ~spl6_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f183])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    v1_funct_1(sK4) | ~spl6_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f91])).
% 0.20/0.51  % (26376)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    r2_hidden(sK5,u1_struct_0(sK2)) | ~spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    spl6_28 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_3 | ~spl6_29 | spl6_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f209,f205,f215,f71,f81,f86,f91,f211])).
% 0.20/0.51  % (26355)Refutation not found, incomplete strategy% (26355)------------------------------
% 0.20/0.51  % (26355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26355)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26355)Memory used [KB]: 10618
% 0.20/0.51  % (26355)Time elapsed: 0.089 s
% 0.20/0.51  % (26355)------------------------------
% 0.20/0.51  % (26355)------------------------------
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl6_6 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl6_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    spl6_3 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    spl6_27 <=> k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK3)) | spl6_27),
% 0.20/0.51    inference(superposition,[],[f207,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | spl6_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f205])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ~spl6_27 | spl6_1 | ~spl6_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f203,f199,f61,f205])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl6_1 <=> k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    spl6_26 <=> k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | (spl6_1 | ~spl6_26)),
% 0.20/0.51    inference(backward_demodulation,[],[f63,f201])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) | ~spl6_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f199])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f61])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    spl6_26 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_15 | ~spl6_16 | spl6_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f197,f141,f136,f131,f126,f121,f116,f106,f96,f91,f86,f81,f76,f199])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl6_4 <=> m1_pre_topc(sK2,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl6_8 <=> m1_pre_topc(sK3,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl6_10 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl6_12 <=> l1_pre_topc(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl6_13 <=> v2_pre_topc(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl6_14 <=> v2_struct_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl6_15 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl6_16 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    spl6_17 <=> v2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_15 | ~spl6_16 | spl6_17)),
% 0.20/0.51    inference(forward_demodulation,[],[f195,f187])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl6_5 | ~spl6_7)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f93,f83,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f81])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_12 | ~spl6_13 | spl6_14 | ~spl6_15 | ~spl6_16 | spl6_17)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f143,f138,f133,f128,f123,f118,f98,f108,f93,f78,f88,f83,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    m1_pre_topc(sK2,sK3) | ~spl6_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f76])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    m1_pre_topc(sK2,sK0) | ~spl6_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f106])).
% 0.20/0.51  % (26368)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    m1_pre_topc(sK3,sK0) | ~spl6_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    l1_pre_topc(sK1) | ~spl6_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f116])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    v2_pre_topc(sK1) | ~spl6_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f121])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ~v2_struct_0(sK1) | spl6_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f126])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl6_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl6_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | spl6_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f141])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    spl6_25 | ~spl6_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f189,f166,f191])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    spl6_21 <=> l1_pre_topc(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    l1_struct_0(sK3) | ~spl6_21),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f168,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  % (26361)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    l1_pre_topc(sK3) | ~spl6_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f166])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl6_24 | ~spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f181,f81,f183])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    v1_relat_1(sK4) | ~spl6_5),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f56,f83,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    spl6_21 | ~spl6_8 | ~spl6_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f164,f131,f96,f166])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    l1_pre_topc(sK3) | (~spl6_8 | ~spl6_15)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f133,f98,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ~spl6_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f141])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    (((((k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r2_hidden(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f32,f31,f30,f29,f28,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) => (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r2_hidden(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    spl6_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f136])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl6_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f131])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~spl6_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f126])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ~v2_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl6_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f121])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    v2_pre_topc(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl6_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f116])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    l1_pre_topc(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl6_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f106])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    m1_pre_topc(sK2,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ~spl6_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f101])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ~v2_struct_0(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl6_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f96])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    m1_pre_topc(sK3,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl6_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f44,f91])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    v1_funct_1(sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl6_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f86])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f81])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f76])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    m1_pre_topc(sK2,sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl6_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f71])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f66])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    r2_hidden(sK5,u1_struct_0(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ~spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f61])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (26358)------------------------------
% 0.20/0.51  % (26358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26358)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (26358)Memory used [KB]: 10874
% 0.20/0.51  % (26358)Time elapsed: 0.092 s
% 0.20/0.51  % (26358)------------------------------
% 0.20/0.51  % (26358)------------------------------
% 0.20/0.51  % (26351)Success in time 0.156 s
%------------------------------------------------------------------------------

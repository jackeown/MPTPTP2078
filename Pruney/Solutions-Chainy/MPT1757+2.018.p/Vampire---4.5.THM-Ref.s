%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 484 expanded)
%              Number of leaves         :   39 ( 165 expanded)
%              Depth                    :   28
%              Number of atoms          : 1634 (3163 expanded)
%              Number of equality atoms :   19 (  90 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f137,f172,f177,f186,f191,f196,f207,f219,f224,f228,f245,f249,f403,f445,f461,f473,f480])).

fof(f480,plain,
    ( spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | spl9_18 ),
    inference(subsumption_resolution,[],[f478,f205])).

fof(f205,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl9_18
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f478,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f477,f190])).

fof(f190,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl9_15
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f477,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f476,f86])).

fof(f86,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl9_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f476,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(resolution,[],[f471,f136])).

fof(f136,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl9_11
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f471,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f470,f116])).

fof(f116,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

% (25143)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (25154)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (25152)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (25153)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (25137)Refutation not found, incomplete strategy% (25137)------------------------------
% (25137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25137)Termination reason: Refutation not found, incomplete strategy

% (25137)Memory used [KB]: 10618
% (25137)Time elapsed: 0.088 s
% (25137)------------------------------
% (25137)------------------------------
% (25155)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f470,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f469,f195])).

fof(f195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl9_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f469,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f468,f185])).

fof(f185,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl9_14
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f468,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f467,f111])).

fof(f111,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl9_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f467,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f466,f106])).

fof(f106,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f466,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f465,f101])).

fof(f101,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f465,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f464,f96])).

fof(f96,plain,
    ( ~ v2_struct_0(sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl9_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f464,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f463,f121])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl9_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f463,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl9_2
    | ~ spl9_17 ),
    inference(resolution,[],[f202,f151])).

fof(f151,plain,
    ( ! [X12,X10,X13,X11] :
        ( ~ r1_tmap_1(X11,X10,sK2,X13)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X10)
        | ~ v1_funct_2(sK2,u1_struct_0(X11),u1_struct_0(X10))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v2_pre_topc(X10)
        | r1_tmap_1(X12,X10,k2_tmap_1(X11,X10,sK2,X12),X13) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f148,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f148,plain,
    ( ! [X12,X10,X13,X11] :
        ( ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X10)
        | ~ v1_funct_2(sK2,u1_struct_0(X11),u1_struct_0(X10))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ r1_tmap_1(X11,X10,sK2,X13)
        | r1_tmap_1(X12,X10,k2_tmap_1(X11,X10,sK2,X12),X13) )
    | ~ spl9_2 ),
    inference(resolution,[],[f91,f78])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f91,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f202,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl9_17
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f473,plain,
    ( ~ spl9_9
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f462,f202])).

fof(f462,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl9_9
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f198,f206])).

fof(f206,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f198,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f42,f126])).

fof(f126,plain,
    ( sK4 = sK5
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_9
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f42,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f461,plain,
    ( spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_22
    | ~ spl9_23
    | ~ spl9_26
    | spl9_27 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_22
    | ~ spl9_23
    | ~ spl9_26
    | spl9_27 ),
    inference(subsumption_resolution,[],[f457,f397])).

fof(f397,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl9_26
  <=> r2_hidden(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f457,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_22
    | ~ spl9_23
    | spl9_27 ),
    inference(subsumption_resolution,[],[f456,f240])).

fof(f240,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl9_22
  <=> v3_pre_topc(u1_struct_0(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f456,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_23
    | spl9_27 ),
    inference(subsumption_resolution,[],[f455,f96])).

fof(f455,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_23
    | spl9_27 ),
    inference(subsumption_resolution,[],[f454,f176])).

fof(f176,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl9_13
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f454,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_23
    | spl9_27 ),
    inference(subsumption_resolution,[],[f453,f243])).

fof(f243,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl9_23
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f453,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl9_4
    | ~ spl9_5
    | spl9_27 ),
    inference(subsumption_resolution,[],[f452,f106])).

fof(f452,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl9_4
    | spl9_27 ),
    inference(subsumption_resolution,[],[f416,f101])).

fof(f416,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | spl9_27 ),
    inference(resolution,[],[f402,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f402,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl9_27 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl9_27
  <=> m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f445,plain,
    ( spl9_1
    | ~ spl9_15
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | spl9_1
    | ~ spl9_15
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_26 ),
    inference(resolution,[],[f437,f190])).

fof(f437,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_15
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_26 ),
    inference(duplicate_literal_removal,[],[f436])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_15
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_26 ),
    inference(resolution,[],[f428,f210])).

fof(f210,plain,
    ( ! [X13] :
        ( m1_connsp_2(sK8(sK3,X13),sK3,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK3)) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl9_19
  <=> ! [X13] :
        ( ~ m1_subset_1(X13,u1_struct_0(sK3))
        | m1_connsp_2(sK8(sK3,X13),sK3,X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f428,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(sK8(sK3,X0),sK3,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_15
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_26 ),
    inference(resolution,[],[f414,f258])).

fof(f258,plain,
    ( ! [X12,X11] :
        ( m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X12,sK3,X11)
        | ~ m1_subset_1(X11,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f257,f213])).

fof(f213,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl9_20
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f257,plain,
    ( ! [X12,X11] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X11,u1_struct_0(sK3))
        | ~ m1_connsp_2(X12,sK3,X11)
        | m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl9_1
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f144,f217])).

fof(f217,plain,
    ( v2_pre_topc(sK3)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl9_21
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f144,plain,
    ( ! [X12,X11] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X11,u1_struct_0(sK3))
        | ~ m1_connsp_2(X12,sK3,X11)
        | m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl9_1 ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f414,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(sK8(sK3,X10),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X10,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_15
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_26 ),
    inference(subsumption_resolution,[],[f408,f190])).

fof(f408,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,X10),k1_zfmisc_1(u1_struct_0(sK3))) )
    | spl9_1
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_26 ),
    inference(resolution,[],[f398,f297])).

fof(f297,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,X1)
        | ~ m1_subset_1(sK8(sK3,X0),k1_zfmisc_1(X1)) )
    | spl9_1
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(resolution,[],[f283,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(sK8(sK3,X0),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(resolution,[],[f279,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f279,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK8(sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_hidden(X0,sK8(sK3,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(resolution,[],[f277,f210])).

fof(f277,plain,
    ( ! [X8,X7] :
        ( ~ m1_connsp_2(X7,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | r2_hidden(X8,X7) )
    | spl9_1
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f276,f258])).

fof(f276,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_connsp_2(X7,sK3,X8)
        | r2_hidden(X8,X7) )
    | spl9_1
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f275,f213])).

fof(f275,plain,
    ( ! [X8,X7] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_connsp_2(X7,sK3,X8)
        | r2_hidden(X8,X7) )
    | spl9_1
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f142,f217])).

fof(f142,plain,
    ( ! [X8,X7] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X8,u1_struct_0(sK3))
        | ~ m1_connsp_2(X7,sK3,X8)
        | r2_hidden(X8,X7) )
    | spl9_1 ),
    inference(resolution,[],[f86,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f398,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl9_26 ),
    inference(avatar_component_clause,[],[f396])).

fof(f403,plain,
    ( ~ spl9_26
    | ~ spl9_27
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f394,f242,f238,f204,f200,f193,f188,f183,f174,f134,f119,f114,f109,f104,f99,f94,f89,f84,f400,f396])).

fof(f394,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f393,f176])).

fof(f393,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f392,f240])).

fof(f392,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f391,f243])).

fof(f391,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18 ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,
    ( ~ m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18 ),
    inference(resolution,[],[f369,f300])).

fof(f300,plain,
    ( ! [X4,X5] :
        ( r1_tarski(sK7(sK1,X4,X5),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r2_hidden(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X4,sK1) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f299,f106])).

fof(f299,plain,
    ( ! [X4,X5] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r2_hidden(X5,X4)
        | r1_tarski(sK7(sK1,X4,X5),X4)
        | ~ v3_pre_topc(X4,sK1) )
    | spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f154,f101])).

fof(f154,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r2_hidden(X5,X4)
        | r1_tarski(sK7(sK1,X4,X5),X4)
        | ~ v3_pre_topc(X4,sK1) )
    | spl9_3 ),
    inference(resolution,[],[f96,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | r1_tarski(sK7(X0,X1,X2),X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f369,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,X0,sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,X0,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f367,f176])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,X0,sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK1,X0,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18 ),
    inference(resolution,[],[f365,f333])).

fof(f333,plain,
    ( ! [X2,X3] :
        ( m1_connsp_2(sK7(sK1,X2,X3),sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ r2_hidden(X3,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X2,sK1) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f332,f106])).

fof(f332,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK7(sK1,X2,X3),sK1,X3)
        | ~ v3_pre_topc(X2,sK1) )
    | spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f153,f101])).

fof(f153,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ r2_hidden(X3,X2)
        | m1_connsp_2(sK7(sK1,X2,X3),sK1,X3)
        | ~ v3_pre_topc(X2,sK1) )
    | spl9_3 ),
    inference(resolution,[],[f96,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(sK7(X0,X1,X2),X0,X2)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK1,sK4)
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f364,f201])).

fof(f201,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f363,f190])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(resolution,[],[f362,f206])).

fof(f362,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f361,f86])).

fof(f361,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,X1)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(resolution,[],[f355,f136])).

fof(f355,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f354,f195])).

fof(f354,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f353,f116])).

fof(f353,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f352,f111])).

fof(f352,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f351,f106])).

fof(f351,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f350,f101])).

fof(f350,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f349,f96])).

fof(f349,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f348,f121])).

fof(f348,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,X2)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2)
        | r1_tmap_1(sK1,sK0,sK2,X2) )
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(resolution,[],[f149,f185])).

fof(f149,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ m1_connsp_2(X3,X1,X4)
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f146,f70])).

fof(f146,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X4,u1_struct_0(X1))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ m1_connsp_2(X3,X1,X4)
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) )
    | ~ spl9_2 ),
    inference(resolution,[],[f91,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f249,plain,
    ( ~ spl9_5
    | ~ spl9_11
    | spl9_23 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_11
    | spl9_23 ),
    inference(subsumption_resolution,[],[f247,f106])).

fof(f247,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl9_11
    | spl9_23 ),
    inference(subsumption_resolution,[],[f246,f136])).

fof(f246,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | spl9_23 ),
    inference(resolution,[],[f244,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f244,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f242])).

fof(f245,plain,
    ( spl9_22
    | ~ spl9_23
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f236,f134,f129,f104,f99,f242,f238])).

fof(f129,plain,
    ( spl9_10
  <=> v1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f236,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f180,f136])).

fof(f180,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f179,f101])).

fof(f179,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl9_5
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f178,f106])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl9_10 ),
    inference(resolution,[],[f131,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f131,plain,
    ( v1_tsep_1(sK3,sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f228,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_11
    | spl9_21 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_11
    | spl9_21 ),
    inference(subsumption_resolution,[],[f226,f101])).

fof(f226,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl9_5
    | ~ spl9_11
    | spl9_21 ),
    inference(subsumption_resolution,[],[f225,f106])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_11
    | spl9_21 ),
    inference(resolution,[],[f221,f136])).

% (25140)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl9_21 ),
    inference(resolution,[],[f218,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f218,plain,
    ( ~ v2_pre_topc(sK3)
    | spl9_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f224,plain,
    ( ~ spl9_5
    | ~ spl9_11
    | spl9_20 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_11
    | spl9_20 ),
    inference(subsumption_resolution,[],[f222,f106])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl9_11
    | spl9_20 ),
    inference(resolution,[],[f220,f136])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_20 ),
    inference(resolution,[],[f214,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f214,plain,
    ( ~ l1_pre_topc(sK3)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f219,plain,
    ( spl9_19
    | ~ spl9_20
    | ~ spl9_21
    | spl9_1 ),
    inference(avatar_split_clause,[],[f145,f84,f216,f212,f209])).

fof(f145,plain,
    ( ! [X13] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X13,u1_struct_0(sK3))
        | m1_connsp_2(sK8(sK3,X13),sK3,X13) )
    | spl9_1 ),
    inference(resolution,[],[f86,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK8(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f207,plain,
    ( spl9_17
    | spl9_18
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f197,f124,f204,f200])).

fof(f197,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f41,f126])).

fof(f41,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f196,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f51,f193])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f191,plain,
    ( spl9_15
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f181,f169,f124,f188])).

fof(f169,plain,
    ( spl9_12
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f181,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f171,f126])).

fof(f171,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f186,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f50,f183])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f177,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f45,f174])).

fof(f45,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f172,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f43,f169])).

fof(f43,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f137,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f48,f134])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f132,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f47,f129])).

fof(f47,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f127,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f44,f124])).

fof(f44,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f57,f119])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f56,f114])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,(
    ~ spl9_6 ),
    inference(avatar_split_clause,[],[f55,f109])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f54,f104])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f49,f89])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (25148)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % (25156)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (25144)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.46  % (25146)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.47  % (25145)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.47  % (25142)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.48  % (25138)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.48  % (25139)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.48  % (25149)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.48  % (25136)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (25137)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (25141)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % (25147)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.49  % (25139)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (25150)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.49  % (25149)Refutation not found, incomplete strategy% (25149)------------------------------
% 0.19/0.49  % (25149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (25149)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (25149)Memory used [KB]: 1791
% 0.19/0.49  % (25149)Time elapsed: 0.050 s
% 0.19/0.49  % (25149)------------------------------
% 0.19/0.49  % (25149)------------------------------
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f481,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f137,f172,f177,f186,f191,f196,f207,f219,f224,f228,f245,f249,f403,f445,f461,f473,f480])).
% 0.19/0.49  fof(f480,plain,(
% 0.19/0.49    spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | spl9_18),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f479])).
% 0.19/0.49  fof(f479,plain,(
% 0.19/0.49    $false | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17 | spl9_18)),
% 0.19/0.49    inference(subsumption_resolution,[],[f478,f205])).
% 0.19/0.49  fof(f205,plain,(
% 0.19/0.49    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl9_18),
% 0.19/0.49    inference(avatar_component_clause,[],[f204])).
% 0.19/0.49  fof(f204,plain,(
% 0.19/0.49    spl9_18 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.19/0.49  fof(f478,plain,(
% 0.19/0.49    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_17)),
% 0.19/0.49    inference(subsumption_resolution,[],[f477,f190])).
% 0.19/0.49  fof(f190,plain,(
% 0.19/0.49    m1_subset_1(sK4,u1_struct_0(sK3)) | ~spl9_15),
% 0.19/0.49    inference(avatar_component_clause,[],[f188])).
% 0.19/0.49  fof(f188,plain,(
% 0.19/0.49    spl9_15 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.19/0.49  fof(f477,plain,(
% 0.19/0.49    ~m1_subset_1(sK4,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_16 | ~spl9_17)),
% 0.19/0.49    inference(subsumption_resolution,[],[f476,f86])).
% 0.19/0.49  fof(f86,plain,(
% 0.19/0.49    ~v2_struct_0(sK3) | spl9_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f84])).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    spl9_1 <=> v2_struct_0(sK3)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.19/0.49  fof(f476,plain,(
% 0.19/0.49    v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_16 | ~spl9_17)),
% 0.19/0.49    inference(resolution,[],[f471,f136])).
% 0.19/0.49  fof(f136,plain,(
% 0.19/0.49    m1_pre_topc(sK3,sK1) | ~spl9_11),
% 0.19/0.49    inference(avatar_component_clause,[],[f134])).
% 0.19/0.49  fof(f134,plain,(
% 0.19/0.49    spl9_11 <=> m1_pre_topc(sK3,sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.19/0.49  fof(f471,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(sK4,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_14 | ~spl9_16 | ~spl9_17)),
% 0.19/0.49    inference(subsumption_resolution,[],[f470,f116])).
% 0.19/0.49  fof(f116,plain,(
% 0.19/0.49    v2_pre_topc(sK0) | ~spl9_7),
% 0.19/0.49    inference(avatar_component_clause,[],[f114])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    spl9_7 <=> v2_pre_topc(sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.19/0.50  % (25143)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.50  % (25154)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.50  % (25152)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.50  % (25153)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.50  % (25137)Refutation not found, incomplete strategy% (25137)------------------------------
% 0.19/0.50  % (25137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (25137)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (25137)Memory used [KB]: 10618
% 0.19/0.50  % (25137)Time elapsed: 0.088 s
% 0.19/0.50  % (25137)------------------------------
% 0.19/0.50  % (25137)------------------------------
% 0.19/0.50  % (25155)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.51  fof(f470,plain,(
% 0.19/0.51    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_14 | ~spl9_16 | ~spl9_17)),
% 0.19/0.51    inference(subsumption_resolution,[],[f469,f195])).
% 0.19/0.51  fof(f195,plain,(
% 0.19/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl9_16),
% 0.19/0.51    inference(avatar_component_clause,[],[f193])).
% 0.19/0.51  fof(f193,plain,(
% 0.19/0.51    spl9_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.19/0.51  fof(f469,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_14 | ~spl9_17)),
% 0.19/0.51    inference(subsumption_resolution,[],[f468,f185])).
% 0.19/0.51  fof(f185,plain,(
% 0.19/0.51    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl9_14),
% 0.19/0.51    inference(avatar_component_clause,[],[f183])).
% 0.19/0.51  fof(f183,plain,(
% 0.19/0.51    spl9_14 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.19/0.51  fof(f468,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_17)),
% 0.19/0.51    inference(subsumption_resolution,[],[f467,f111])).
% 0.19/0.51  fof(f111,plain,(
% 0.19/0.51    ~v2_struct_0(sK0) | spl9_6),
% 0.19/0.51    inference(avatar_component_clause,[],[f109])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    spl9_6 <=> v2_struct_0(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.19/0.51  fof(f467,plain,(
% 0.19/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_8 | ~spl9_17)),
% 0.19/0.51    inference(subsumption_resolution,[],[f466,f106])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    l1_pre_topc(sK1) | ~spl9_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f104])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    spl9_5 <=> l1_pre_topc(sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.19/0.51  fof(f466,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_17)),
% 0.19/0.51    inference(subsumption_resolution,[],[f465,f101])).
% 0.19/0.51  fof(f101,plain,(
% 0.19/0.51    v2_pre_topc(sK1) | ~spl9_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f99])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    spl9_4 <=> v2_pre_topc(sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.19/0.51  fof(f465,plain,(
% 0.19/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_8 | ~spl9_17)),
% 0.19/0.51    inference(subsumption_resolution,[],[f464,f96])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    ~v2_struct_0(sK1) | spl9_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f94])).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    spl9_3 <=> v2_struct_0(sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.19/0.51  fof(f464,plain,(
% 0.19/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | ~spl9_8 | ~spl9_17)),
% 0.19/0.51    inference(subsumption_resolution,[],[f463,f121])).
% 0.19/0.51  fof(f121,plain,(
% 0.19/0.51    l1_pre_topc(sK0) | ~spl9_8),
% 0.19/0.51    inference(avatar_component_clause,[],[f119])).
% 0.19/0.51  fof(f119,plain,(
% 0.19/0.51    spl9_8 <=> l1_pre_topc(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.19/0.51  fof(f463,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | (~spl9_2 | ~spl9_17)),
% 0.19/0.51    inference(resolution,[],[f202,f151])).
% 0.19/0.51  fof(f151,plain,(
% 0.19/0.51    ( ! [X12,X10,X13,X11] : (~r1_tmap_1(X11,X10,sK2,X13) | ~l1_pre_topc(X10) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(X10) | ~v1_funct_2(sK2,u1_struct_0(X11),u1_struct_0(X10)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10)))) | v2_struct_0(X12) | ~m1_pre_topc(X12,X11) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~v2_pre_topc(X10) | r1_tmap_1(X12,X10,k2_tmap_1(X11,X10,sK2,X12),X13)) ) | ~spl9_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f148,f70])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.19/0.51  fof(f148,plain,(
% 0.19/0.51    ( ! [X12,X10,X13,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(X10) | ~v1_funct_2(sK2,u1_struct_0(X11),u1_struct_0(X10)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10)))) | v2_struct_0(X12) | ~m1_pre_topc(X12,X11) | ~m1_subset_1(X13,u1_struct_0(X11)) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~r1_tmap_1(X11,X10,sK2,X13) | r1_tmap_1(X12,X10,k2_tmap_1(X11,X10,sK2,X12),X13)) ) | ~spl9_2),
% 0.19/0.51    inference(resolution,[],[f91,f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.19/0.51    inference(equality_resolution,[],[f67])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.19/0.51  fof(f91,plain,(
% 0.19/0.51    v1_funct_1(sK2) | ~spl9_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f89])).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    spl9_2 <=> v1_funct_1(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.19/0.51  fof(f202,plain,(
% 0.19/0.51    r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl9_17),
% 0.19/0.51    inference(avatar_component_clause,[],[f200])).
% 0.19/0.51  fof(f200,plain,(
% 0.19/0.51    spl9_17 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.19/0.51  fof(f473,plain,(
% 0.19/0.51    ~spl9_9 | ~spl9_17 | ~spl9_18),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f472])).
% 0.19/0.51  fof(f472,plain,(
% 0.19/0.51    $false | (~spl9_9 | ~spl9_17 | ~spl9_18)),
% 0.19/0.51    inference(subsumption_resolution,[],[f462,f202])).
% 0.19/0.51  fof(f462,plain,(
% 0.19/0.51    ~r1_tmap_1(sK1,sK0,sK2,sK4) | (~spl9_9 | ~spl9_18)),
% 0.19/0.51    inference(subsumption_resolution,[],[f198,f206])).
% 0.19/0.51  fof(f206,plain,(
% 0.19/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl9_18),
% 0.19/0.51    inference(avatar_component_clause,[],[f204])).
% 0.19/0.51  fof(f198,plain,(
% 0.19/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl9_9),
% 0.19/0.51    inference(forward_demodulation,[],[f42,f126])).
% 0.19/0.51  fof(f126,plain,(
% 0.19/0.51    sK4 = sK5 | ~spl9_9),
% 0.19/0.51    inference(avatar_component_clause,[],[f124])).
% 0.19/0.51  fof(f124,plain,(
% 0.19/0.51    spl9_9 <=> sK4 = sK5),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,negated_conjecture,(
% 0.19/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.19/0.51    inference(negated_conjecture,[],[f14])).
% 0.19/0.51  fof(f14,conjecture,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.19/0.51  fof(f461,plain,(
% 0.19/0.51    spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_22 | ~spl9_23 | ~spl9_26 | spl9_27),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f460])).
% 0.19/0.51  fof(f460,plain,(
% 0.19/0.51    $false | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_22 | ~spl9_23 | ~spl9_26 | spl9_27)),
% 0.19/0.51    inference(subsumption_resolution,[],[f457,f397])).
% 0.19/0.51  fof(f397,plain,(
% 0.19/0.51    r2_hidden(sK4,u1_struct_0(sK3)) | ~spl9_26),
% 0.19/0.51    inference(avatar_component_clause,[],[f396])).
% 0.19/0.51  fof(f396,plain,(
% 0.19/0.51    spl9_26 <=> r2_hidden(sK4,u1_struct_0(sK3))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.19/0.51  fof(f457,plain,(
% 0.19/0.51    ~r2_hidden(sK4,u1_struct_0(sK3)) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_22 | ~spl9_23 | spl9_27)),
% 0.19/0.51    inference(subsumption_resolution,[],[f456,f240])).
% 0.19/0.51  fof(f240,plain,(
% 0.19/0.51    v3_pre_topc(u1_struct_0(sK3),sK1) | ~spl9_22),
% 0.19/0.51    inference(avatar_component_clause,[],[f238])).
% 0.19/0.51  fof(f238,plain,(
% 0.19/0.51    spl9_22 <=> v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.19/0.51  fof(f456,plain,(
% 0.19/0.51    ~r2_hidden(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_23 | spl9_27)),
% 0.19/0.51    inference(subsumption_resolution,[],[f455,f96])).
% 0.19/0.51  fof(f455,plain,(
% 0.19/0.51    ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_23 | spl9_27)),
% 0.19/0.51    inference(subsumption_resolution,[],[f454,f176])).
% 0.19/0.51  fof(f176,plain,(
% 0.19/0.51    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl9_13),
% 0.19/0.51    inference(avatar_component_clause,[],[f174])).
% 0.19/0.51  fof(f174,plain,(
% 0.19/0.51    spl9_13 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.19/0.51  fof(f454,plain,(
% 0.19/0.51    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl9_4 | ~spl9_5 | ~spl9_23 | spl9_27)),
% 0.19/0.51    inference(subsumption_resolution,[],[f453,f243])).
% 0.19/0.51  fof(f243,plain,(
% 0.19/0.51    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl9_23),
% 0.19/0.51    inference(avatar_component_clause,[],[f242])).
% 0.19/0.51  fof(f242,plain,(
% 0.19/0.51    spl9_23 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.19/0.51  fof(f453,plain,(
% 0.19/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl9_4 | ~spl9_5 | spl9_27)),
% 0.19/0.51    inference(subsumption_resolution,[],[f452,f106])).
% 0.19/0.51  fof(f452,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl9_4 | spl9_27)),
% 0.19/0.51    inference(subsumption_resolution,[],[f416,f101])).
% 0.19/0.51  fof(f416,plain,(
% 0.19/0.51    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | v2_struct_0(sK1) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | spl9_27),
% 0.19/0.51    inference(resolution,[],[f402,f61])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.19/0.51  fof(f402,plain,(
% 0.19/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | spl9_27),
% 0.19/0.51    inference(avatar_component_clause,[],[f400])).
% 0.19/0.51  fof(f400,plain,(
% 0.19/0.51    spl9_27 <=> m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.19/0.51  fof(f445,plain,(
% 0.19/0.51    spl9_1 | ~spl9_15 | ~spl9_19 | ~spl9_20 | ~spl9_21 | spl9_26),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f443])).
% 0.19/0.51  fof(f443,plain,(
% 0.19/0.51    $false | (spl9_1 | ~spl9_15 | ~spl9_19 | ~spl9_20 | ~spl9_21 | spl9_26)),
% 0.19/0.51    inference(resolution,[],[f437,f190])).
% 0.19/0.51  fof(f437,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_15 | ~spl9_19 | ~spl9_20 | ~spl9_21 | spl9_26)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f436])).
% 0.19/0.51  fof(f436,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_15 | ~spl9_19 | ~spl9_20 | ~spl9_21 | spl9_26)),
% 0.19/0.51    inference(resolution,[],[f428,f210])).
% 0.19/0.51  fof(f210,plain,(
% 0.19/0.51    ( ! [X13] : (m1_connsp_2(sK8(sK3,X13),sK3,X13) | ~m1_subset_1(X13,u1_struct_0(sK3))) ) | ~spl9_19),
% 0.19/0.51    inference(avatar_component_clause,[],[f209])).
% 0.19/0.51  fof(f209,plain,(
% 0.19/0.51    spl9_19 <=> ! [X13] : (~m1_subset_1(X13,u1_struct_0(sK3)) | m1_connsp_2(sK8(sK3,X13),sK3,X13))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.19/0.51  fof(f428,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_connsp_2(sK8(sK3,X0),sK3,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_15 | ~spl9_19 | ~spl9_20 | ~spl9_21 | spl9_26)),
% 0.19/0.51    inference(resolution,[],[f414,f258])).
% 0.19/0.51  fof(f258,plain,(
% 0.19/0.51    ( ! [X12,X11] : (m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X12,sK3,X11) | ~m1_subset_1(X11,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_20 | ~spl9_21)),
% 0.19/0.51    inference(subsumption_resolution,[],[f257,f213])).
% 0.19/0.51  fof(f213,plain,(
% 0.19/0.51    l1_pre_topc(sK3) | ~spl9_20),
% 0.19/0.51    inference(avatar_component_clause,[],[f212])).
% 0.19/0.51  fof(f212,plain,(
% 0.19/0.51    spl9_20 <=> l1_pre_topc(sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.19/0.51  fof(f257,plain,(
% 0.19/0.51    ( ! [X12,X11] : (~l1_pre_topc(sK3) | ~m1_subset_1(X11,u1_struct_0(sK3)) | ~m1_connsp_2(X12,sK3,X11) | m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK3)))) ) | (spl9_1 | ~spl9_21)),
% 0.19/0.51    inference(subsumption_resolution,[],[f144,f217])).
% 0.19/0.51  fof(f217,plain,(
% 0.19/0.51    v2_pre_topc(sK3) | ~spl9_21),
% 0.19/0.51    inference(avatar_component_clause,[],[f216])).
% 0.19/0.51  fof(f216,plain,(
% 0.19/0.51    spl9_21 <=> v2_pre_topc(sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.19/0.51  fof(f144,plain,(
% 0.19/0.51    ( ! [X12,X11] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X11,u1_struct_0(sK3)) | ~m1_connsp_2(X12,sK3,X11) | m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK3)))) ) | spl9_1),
% 0.19/0.51    inference(resolution,[],[f86,f75])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.19/0.51  fof(f414,plain,(
% 0.19/0.51    ( ! [X10] : (~m1_subset_1(sK8(sK3,X10),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X10,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_15 | ~spl9_19 | ~spl9_20 | ~spl9_21 | spl9_26)),
% 0.19/0.51    inference(subsumption_resolution,[],[f408,f190])).
% 0.19/0.51  fof(f408,plain,(
% 0.19/0.51    ( ! [X10] : (~m1_subset_1(X10,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK8(sK3,X10),k1_zfmisc_1(u1_struct_0(sK3)))) ) | (spl9_1 | ~spl9_19 | ~spl9_20 | ~spl9_21 | spl9_26)),
% 0.19/0.51    inference(resolution,[],[f398,f297])).
% 0.19/0.51  fof(f297,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X2,X1) | ~m1_subset_1(sK8(sK3,X0),k1_zfmisc_1(X1))) ) | (spl9_1 | ~spl9_19 | ~spl9_20 | ~spl9_21)),
% 0.19/0.51    inference(resolution,[],[f283,f74])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.51  fof(f283,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(sK8(sK3,X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_19 | ~spl9_20 | ~spl9_21)),
% 0.19/0.51    inference(resolution,[],[f279,f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.51  fof(f279,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(X0,sK8(sK3,X0)) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_19 | ~spl9_20 | ~spl9_21)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f278])).
% 0.19/0.51  fof(f278,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r2_hidden(X0,sK8(sK3,X0)) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_19 | ~spl9_20 | ~spl9_21)),
% 0.19/0.51    inference(resolution,[],[f277,f210])).
% 0.19/0.51  fof(f277,plain,(
% 0.19/0.51    ( ! [X8,X7] : (~m1_connsp_2(X7,sK3,X8) | ~m1_subset_1(X8,u1_struct_0(sK3)) | r2_hidden(X8,X7)) ) | (spl9_1 | ~spl9_20 | ~spl9_21)),
% 0.19/0.51    inference(subsumption_resolution,[],[f276,f258])).
% 0.19/0.51  fof(f276,plain,(
% 0.19/0.51    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_connsp_2(X7,sK3,X8) | r2_hidden(X8,X7)) ) | (spl9_1 | ~spl9_20 | ~spl9_21)),
% 0.19/0.51    inference(subsumption_resolution,[],[f275,f213])).
% 0.19/0.51  fof(f275,plain,(
% 0.19/0.51    ( ! [X8,X7] : (~l1_pre_topc(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_connsp_2(X7,sK3,X8) | r2_hidden(X8,X7)) ) | (spl9_1 | ~spl9_21)),
% 0.19/0.51    inference(subsumption_resolution,[],[f142,f217])).
% 0.19/0.51  fof(f142,plain,(
% 0.19/0.51    ( ! [X8,X7] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X8,u1_struct_0(sK3)) | ~m1_connsp_2(X7,sK3,X8) | r2_hidden(X8,X7)) ) | spl9_1),
% 0.19/0.51    inference(resolution,[],[f86,f66])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.19/0.51  fof(f398,plain,(
% 0.19/0.51    ~r2_hidden(sK4,u1_struct_0(sK3)) | spl9_26),
% 0.19/0.51    inference(avatar_component_clause,[],[f396])).
% 0.19/0.51  fof(f403,plain,(
% 0.19/0.51    ~spl9_26 | ~spl9_27 | spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18 | ~spl9_22 | ~spl9_23),
% 0.19/0.51    inference(avatar_split_clause,[],[f394,f242,f238,f204,f200,f193,f188,f183,f174,f134,f119,f114,f109,f104,f99,f94,f89,f84,f400,f396])).
% 0.19/0.51  fof(f394,plain,(
% 0.19/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18 | ~spl9_22 | ~spl9_23)),
% 0.19/0.51    inference(subsumption_resolution,[],[f393,f176])).
% 0.19/0.51  fof(f393,plain,(
% 0.19/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18 | ~spl9_22 | ~spl9_23)),
% 0.19/0.51    inference(subsumption_resolution,[],[f392,f240])).
% 0.19/0.51  fof(f392,plain,(
% 0.19/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18 | ~spl9_23)),
% 0.19/0.51    inference(subsumption_resolution,[],[f391,f243])).
% 0.19/0.51  fof(f391,plain,(
% 0.19/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18)),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f390])).
% 0.19/0.51  fof(f390,plain,(
% 0.19/0.51    ~m1_subset_1(sK7(sK1,u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18)),
% 0.19/0.51    inference(resolution,[],[f369,f300])).
% 0.19/0.51  fof(f300,plain,(
% 0.19/0.51    ( ! [X4,X5] : (r1_tarski(sK7(sK1,X4,X5),X4) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~r2_hidden(X5,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X4,sK1)) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.19/0.51    inference(subsumption_resolution,[],[f299,f106])).
% 0.19/0.51  fof(f299,plain,(
% 0.19/0.51    ( ! [X4,X5] : (~l1_pre_topc(sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~r2_hidden(X5,X4) | r1_tarski(sK7(sK1,X4,X5),X4) | ~v3_pre_topc(X4,sK1)) ) | (spl9_3 | ~spl9_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f154,f101])).
% 0.19/0.51  fof(f154,plain,(
% 0.19/0.51    ( ! [X4,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~r2_hidden(X5,X4) | r1_tarski(sK7(sK1,X4,X5),X4) | ~v3_pre_topc(X4,sK1)) ) | spl9_3),
% 0.19/0.51    inference(resolution,[],[f96,f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_tarski(sK7(X0,X1,X2),X1) | ~v3_pre_topc(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f369,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(sK7(sK1,X0,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,X0,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18)),
% 0.19/0.51    inference(subsumption_resolution,[],[f367,f176])).
% 0.19/0.51  fof(f367,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(sK7(sK1,X0,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK7(sK1,X0,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18)),
% 0.19/0.51    inference(resolution,[],[f365,f333])).
% 0.19/0.51  fof(f333,plain,(
% 0.19/0.51    ( ! [X2,X3] : (m1_connsp_2(sK7(sK1,X2,X3),sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X2,sK1)) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.19/0.51    inference(subsumption_resolution,[],[f332,f106])).
% 0.19/0.51  fof(f332,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~l1_pre_topc(sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK7(sK1,X2,X3),sK1,X3) | ~v3_pre_topc(X2,sK1)) ) | (spl9_3 | ~spl9_4)),
% 0.19/0.51    inference(subsumption_resolution,[],[f153,f101])).
% 0.19/0.51  fof(f153,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(X3,X2) | m1_connsp_2(sK7(sK1,X2,X3),sK1,X3) | ~v3_pre_topc(X2,sK1)) ) | spl9_3),
% 0.19/0.51    inference(resolution,[],[f96,f62])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK7(X0,X1,X2),X0,X2) | ~v3_pre_topc(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f365,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK1,sK4) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_15 | ~spl9_16 | spl9_17 | ~spl9_18)),
% 0.19/0.51    inference(subsumption_resolution,[],[f364,f201])).
% 0.19/0.51  fof(f201,plain,(
% 0.19/0.51    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl9_17),
% 0.19/0.51    inference(avatar_component_clause,[],[f200])).
% 0.19/0.51  fof(f364,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_15 | ~spl9_16 | ~spl9_18)),
% 0.19/0.51    inference(subsumption_resolution,[],[f363,f190])).
% 0.19/0.51  fof(f363,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_16 | ~spl9_18)),
% 0.19/0.51    inference(resolution,[],[f362,f206])).
% 0.19/0.51  fof(f362,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_16)),
% 0.19/0.51    inference(subsumption_resolution,[],[f361,f86])).
% 0.19/0.51  fof(f361,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,X1) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_14 | ~spl9_16)),
% 0.19/0.51    inference(resolution,[],[f355,f136])).
% 0.19/0.51  fof(f355,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_14 | ~spl9_16)),
% 0.19/0.51    inference(subsumption_resolution,[],[f354,f195])).
% 0.19/0.51  fof(f354,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_14)),
% 0.19/0.51    inference(subsumption_resolution,[],[f353,f116])).
% 0.19/0.51  fof(f353,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_14)),
% 0.19/0.51    inference(subsumption_resolution,[],[f352,f111])).
% 0.19/0.51  fof(f352,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_8 | ~spl9_14)),
% 0.19/0.51    inference(subsumption_resolution,[],[f351,f106])).
% 0.19/0.51  fof(f351,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_14)),
% 0.19/0.51    inference(subsumption_resolution,[],[f350,f101])).
% 0.19/0.51  fof(f350,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | spl9_3 | ~spl9_8 | ~spl9_14)),
% 0.19/0.51    inference(subsumption_resolution,[],[f349,f96])).
% 0.19/0.51  fof(f349,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | ~spl9_8 | ~spl9_14)),
% 0.19/0.51    inference(subsumption_resolution,[],[f348,f121])).
% 0.19/0.51  fof(f348,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,X2) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) ) | (~spl9_2 | ~spl9_14)),
% 0.19/0.51    inference(resolution,[],[f149,f185])).
% 0.19/0.51  fof(f149,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) ) | ~spl9_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f146,f70])).
% 0.19/0.51  fof(f146,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) ) | ~spl9_2),
% 0.19/0.51    inference(resolution,[],[f91,f80])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.19/0.51    inference(equality_resolution,[],[f68])).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.19/0.51  fof(f249,plain,(
% 0.19/0.51    ~spl9_5 | ~spl9_11 | spl9_23),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f248])).
% 0.19/0.51  fof(f248,plain,(
% 0.19/0.51    $false | (~spl9_5 | ~spl9_11 | spl9_23)),
% 0.19/0.51    inference(subsumption_resolution,[],[f247,f106])).
% 0.19/0.51  fof(f247,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | (~spl9_11 | spl9_23)),
% 0.19/0.51    inference(subsumption_resolution,[],[f246,f136])).
% 0.19/0.51  fof(f246,plain,(
% 0.19/0.51    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | spl9_23),
% 0.19/0.51    inference(resolution,[],[f244,f59])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.19/0.51  fof(f244,plain,(
% 0.19/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl9_23),
% 0.19/0.51    inference(avatar_component_clause,[],[f242])).
% 0.19/0.51  fof(f245,plain,(
% 0.19/0.51    spl9_22 | ~spl9_23 | ~spl9_4 | ~spl9_5 | ~spl9_10 | ~spl9_11),
% 0.19/0.51    inference(avatar_split_clause,[],[f236,f134,f129,f104,f99,f242,f238])).
% 0.19/0.51  fof(f129,plain,(
% 0.19/0.51    spl9_10 <=> v1_tsep_1(sK3,sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.19/0.51  fof(f236,plain,(
% 0.19/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl9_4 | ~spl9_5 | ~spl9_10 | ~spl9_11)),
% 0.19/0.51    inference(subsumption_resolution,[],[f180,f136])).
% 0.19/0.51  fof(f180,plain,(
% 0.19/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1) | (~spl9_4 | ~spl9_5 | ~spl9_10)),
% 0.19/0.51    inference(subsumption_resolution,[],[f179,f101])).
% 0.19/0.51  fof(f179,plain,(
% 0.19/0.51    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | (~spl9_5 | ~spl9_10)),
% 0.19/0.51    inference(subsumption_resolution,[],[f178,f106])).
% 0.19/0.51  fof(f178,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | ~spl9_10),
% 0.19/0.51    inference(resolution,[],[f131,f82])).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f72])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.51    inference(flattening,[],[f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.19/0.51  fof(f131,plain,(
% 0.19/0.51    v1_tsep_1(sK3,sK1) | ~spl9_10),
% 0.19/0.51    inference(avatar_component_clause,[],[f129])).
% 0.19/0.51  fof(f228,plain,(
% 0.19/0.51    ~spl9_4 | ~spl9_5 | ~spl9_11 | spl9_21),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f227])).
% 0.19/0.51  fof(f227,plain,(
% 0.19/0.51    $false | (~spl9_4 | ~spl9_5 | ~spl9_11 | spl9_21)),
% 0.19/0.51    inference(subsumption_resolution,[],[f226,f101])).
% 0.19/0.51  fof(f226,plain,(
% 0.19/0.51    ~v2_pre_topc(sK1) | (~spl9_5 | ~spl9_11 | spl9_21)),
% 0.19/0.51    inference(subsumption_resolution,[],[f225,f106])).
% 0.19/0.51  fof(f225,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_11 | spl9_21)),
% 0.19/0.51    inference(resolution,[],[f221,f136])).
% 0.19/0.51  % (25140)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.51  fof(f221,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl9_21),
% 0.19/0.51    inference(resolution,[],[f218,f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.51    inference(flattening,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.19/0.51  fof(f218,plain,(
% 0.19/0.51    ~v2_pre_topc(sK3) | spl9_21),
% 0.19/0.51    inference(avatar_component_clause,[],[f216])).
% 0.19/0.51  fof(f224,plain,(
% 0.19/0.51    ~spl9_5 | ~spl9_11 | spl9_20),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f223])).
% 0.19/0.51  fof(f223,plain,(
% 0.19/0.51    $false | (~spl9_5 | ~spl9_11 | spl9_20)),
% 0.19/0.51    inference(subsumption_resolution,[],[f222,f106])).
% 0.19/0.51  fof(f222,plain,(
% 0.19/0.51    ~l1_pre_topc(sK1) | (~spl9_11 | spl9_20)),
% 0.19/0.51    inference(resolution,[],[f220,f136])).
% 0.19/0.51  fof(f220,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl9_20),
% 0.19/0.51    inference(resolution,[],[f214,f58])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.51  fof(f214,plain,(
% 0.19/0.51    ~l1_pre_topc(sK3) | spl9_20),
% 0.19/0.51    inference(avatar_component_clause,[],[f212])).
% 0.19/0.51  fof(f219,plain,(
% 0.19/0.51    spl9_19 | ~spl9_20 | ~spl9_21 | spl9_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f145,f84,f216,f212,f209])).
% 0.19/0.51  fof(f145,plain,(
% 0.19/0.51    ( ! [X13] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X13,u1_struct_0(sK3)) | m1_connsp_2(sK8(sK3,X13),sK3,X13)) ) | spl9_1),
% 0.19/0.51    inference(resolution,[],[f86,f76])).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK8(X0,X1),X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.19/0.51  fof(f207,plain,(
% 0.19/0.51    spl9_17 | spl9_18 | ~spl9_9),
% 0.19/0.51    inference(avatar_split_clause,[],[f197,f124,f204,f200])).
% 0.19/0.51  fof(f197,plain,(
% 0.19/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl9_9),
% 0.19/0.51    inference(forward_demodulation,[],[f41,f126])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f196,plain,(
% 0.19/0.51    spl9_16),
% 0.19/0.51    inference(avatar_split_clause,[],[f51,f193])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f191,plain,(
% 0.19/0.51    spl9_15 | ~spl9_9 | ~spl9_12),
% 0.19/0.51    inference(avatar_split_clause,[],[f181,f169,f124,f188])).
% 0.19/0.51  fof(f169,plain,(
% 0.19/0.51    spl9_12 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.19/0.51  fof(f181,plain,(
% 0.19/0.51    m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_9 | ~spl9_12)),
% 0.19/0.51    inference(forward_demodulation,[],[f171,f126])).
% 0.19/0.51  fof(f171,plain,(
% 0.19/0.51    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_12),
% 0.19/0.51    inference(avatar_component_clause,[],[f169])).
% 0.19/0.51  fof(f186,plain,(
% 0.19/0.51    spl9_14),
% 0.19/0.51    inference(avatar_split_clause,[],[f50,f183])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f177,plain,(
% 0.19/0.51    spl9_13),
% 0.19/0.51    inference(avatar_split_clause,[],[f45,f174])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f172,plain,(
% 0.19/0.51    spl9_12),
% 0.19/0.51    inference(avatar_split_clause,[],[f43,f169])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f137,plain,(
% 0.19/0.51    spl9_11),
% 0.19/0.51    inference(avatar_split_clause,[],[f48,f134])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    m1_pre_topc(sK3,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    spl9_10),
% 0.19/0.51    inference(avatar_split_clause,[],[f47,f129])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    v1_tsep_1(sK3,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f127,plain,(
% 0.19/0.51    spl9_9),
% 0.19/0.51    inference(avatar_split_clause,[],[f44,f124])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    sK4 = sK5),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f122,plain,(
% 0.19/0.51    spl9_8),
% 0.19/0.51    inference(avatar_split_clause,[],[f57,f119])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    l1_pre_topc(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    spl9_7),
% 0.19/0.51    inference(avatar_split_clause,[],[f56,f114])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    v2_pre_topc(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    ~spl9_6),
% 0.19/0.51    inference(avatar_split_clause,[],[f55,f109])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    ~v2_struct_0(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f107,plain,(
% 0.19/0.51    spl9_5),
% 0.19/0.51    inference(avatar_split_clause,[],[f54,f104])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    l1_pre_topc(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    spl9_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f53,f99])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    v2_pre_topc(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f97,plain,(
% 0.19/0.51    ~spl9_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f52,f94])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ~v2_struct_0(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    spl9_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f49,f89])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    v1_funct_1(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    ~spl9_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f46,f84])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ~v2_struct_0(sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (25139)------------------------------
% 0.19/0.51  % (25139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (25139)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (25139)Memory used [KB]: 10874
% 0.19/0.51  % (25139)Time elapsed: 0.091 s
% 0.19/0.51  % (25139)------------------------------
% 0.19/0.51  % (25139)------------------------------
% 0.19/0.51  % (25135)Success in time 0.158 s
%------------------------------------------------------------------------------

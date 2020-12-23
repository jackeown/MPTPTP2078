%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t151_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:10 EDT 2019

% Result     : Theorem 16.70s
% Output     : Refutation 16.70s
% Verified   : 
% Statistics : Number of formulae       :  404 (1140 expanded)
%              Number of leaves         :   70 ( 512 expanded)
%              Depth                    :   33
%              Number of atoms          : 3832 (13135 expanded)
%              Number of equality atoms :   74 ( 423 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5827,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f238,f245,f252,f259,f266,f273,f280,f287,f294,f301,f308,f315,f322,f329,f336,f343,f350,f357,f364,f371,f378,f385,f392,f416,f423,f438,f446,f458,f466,f526,f536,f673,f923,f1580,f2202,f2546,f2564,f4514,f4543,f4569,f4633,f4737,f4839,f5824,f5825,f5826])).

fof(f5826,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(theory_axiom,[])).

fof(f5825,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v5_pre_topc(sK4,sK2,sK1) ),
    introduced(theory_axiom,[])).

fof(f5824,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_88
    | spl11_249 ),
    inference(avatar_contradiction_clause,[],[f5823])).

fof(f5823,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_88
    | ~ spl11_249 ),
    inference(subsumption_resolution,[],[f5822,f422])).

fof(f422,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl11_58
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f5822,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_56
    | ~ spl11_88
    | ~ spl11_249 ),
    inference(subsumption_resolution,[],[f5821,f415])).

fof(f415,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl11_56
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f5821,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_88
    | ~ spl11_249 ),
    inference(subsumption_resolution,[],[f5820,f216])).

fof(f216,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl11_0
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f5820,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_88
    | ~ spl11_249 ),
    inference(subsumption_resolution,[],[f5819,f222])).

fof(f222,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl11_2
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f5819,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_88
    | ~ spl11_249 ),
    inference(subsumption_resolution,[],[f5818,f234])).

fof(f234,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl11_6
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f5818,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_88
    | ~ spl11_249 ),
    inference(subsumption_resolution,[],[f5814,f535])).

fof(f535,plain,
    ( l1_struct_0(sK2)
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl11_88
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f5814,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_249 ),
    inference(resolution,[],[f4562,f175])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',dt_k2_tmap_1)).

fof(f4562,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_249 ),
    inference(avatar_component_clause,[],[f4561])).

fof(f4561,plain,
    ( spl11_249
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_249])])).

fof(f4839,plain,
    ( ~ spl11_249
    | ~ spl11_259
    | ~ spl11_261
    | ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30
    | ~ spl11_32
    | spl11_35
    | ~ spl11_36
    | spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(avatar_split_clause,[],[f4826,f4552,f4512,f390,f383,f376,f369,f362,f355,f348,f341,f334,f327,f320,f285,f278,f271,f264,f243,f233,f230,f221,f215,f4837,f4831,f4561])).

fof(f4831,plain,
    ( spl11_259
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_259])])).

fof(f4837,plain,
    ( spl11_261
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_261])])).

fof(f230,plain,
    ( spl11_5
  <=> ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f243,plain,
    ( spl11_8
  <=> r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f264,plain,
    ( spl11_14
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f271,plain,
    ( spl11_16
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f278,plain,
    ( spl11_18
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f285,plain,
    ( spl11_20
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f320,plain,
    ( spl11_30
  <=> k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f327,plain,
    ( spl11_32
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f334,plain,
    ( spl11_35
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f341,plain,
    ( spl11_36
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f348,plain,
    ( spl11_39
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f355,plain,
    ( spl11_40
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f362,plain,
    ( spl11_42
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f369,plain,
    ( spl11_45
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f376,plain,
    ( spl11_46
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f383,plain,
    ( spl11_48
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f390,plain,
    ( spl11_51
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f4512,plain,
    ( spl11_244
  <=> k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_244])])).

fof(f4552,plain,
    ( spl11_246
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_246])])).

fof(f4826,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4825,f286])).

fof(f286,plain,
    ( v1_funct_1(sK5)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f285])).

fof(f4825,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(forward_demodulation,[],[f4824,f4513])).

fof(f4513,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ spl11_244 ),
    inference(avatar_component_clause,[],[f4512])).

fof(f4824,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4823,f279])).

fof(f279,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f278])).

fof(f4823,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(forward_demodulation,[],[f4822,f4513])).

fof(f4822,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4821,f272])).

fof(f272,plain,
    ( v5_pre_topc(sK5,sK3,sK1)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f271])).

fof(f4821,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(forward_demodulation,[],[f4820,f4513])).

fof(f4820,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4819,f370])).

fof(f370,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f369])).

fof(f4819,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4818,f363])).

fof(f363,plain,
    ( v2_pre_topc(sK1)
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f362])).

fof(f4818,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4817,f356])).

fof(f356,plain,
    ( l1_pre_topc(sK1)
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f355])).

fof(f4817,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4816,f216])).

fof(f4816,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4815,f222])).

fof(f4815,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4814,f234])).

fof(f4814,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_5
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4813,f231])).

fof(f231,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f230])).

fof(f4813,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244
    | ~ spl11_246 ),
    inference(subsumption_resolution,[],[f4812,f4553])).

fof(f4553,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ spl11_246 ),
    inference(avatar_component_clause,[],[f4552])).

fof(f4812,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244 ),
    inference(subsumption_resolution,[],[f4753,f265])).

fof(f265,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f264])).

fof(f4753,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_244 ),
    inference(superposition,[],[f1095,f4513])).

fof(f1095,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1094,f391])).

fof(f391,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f390])).

fof(f1094,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1093,f384])).

fof(f384,plain,
    ( v2_pre_topc(sK0)
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f383])).

fof(f1093,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f1092,f377])).

fof(f377,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f376])).

fof(f1092,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f1091,f349])).

fof(f349,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f348])).

fof(f1091,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f1090,f342])).

fof(f342,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f341])).

fof(f1090,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f1089,f335])).

fof(f335,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f334])).

fof(f1089,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_8
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f1088,f328])).

fof(f328,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f327])).

fof(f1088,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_8
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f1087,f244])).

fof(f244,plain,
    ( r4_tsep_1(sK0,sK2,sK3)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1087,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | ~ r4_tsep_1(sK0,sK2,sK3)
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30 ),
    inference(trivial_inequality_removal,[],[f1082])).

fof(f1082,plain,
    ( ! [X0,X1] :
        ( sK0 != sK0
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK3),sK3,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK3),u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK3))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK2),sK2,X0)
        | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK2))
        | ~ r4_tsep_1(sK0,sK2,sK3)
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30 ),
    inference(superposition,[],[f154,f321])).

fof(f321,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f320])).

fof(f154,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ r4_tsep_1(X0,X3,X4)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',t132_tmap_1)).

fof(f4737,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_86
    | spl11_243 ),
    inference(avatar_contradiction_clause,[],[f4736])).

fof(f4736,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_86
    | ~ spl11_243 ),
    inference(subsumption_resolution,[],[f4735,f422])).

fof(f4735,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_56
    | ~ spl11_86
    | ~ spl11_243 ),
    inference(subsumption_resolution,[],[f4734,f415])).

fof(f4734,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_86
    | ~ spl11_243 ),
    inference(subsumption_resolution,[],[f4733,f216])).

fof(f4733,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_86
    | ~ spl11_243 ),
    inference(subsumption_resolution,[],[f4732,f222])).

fof(f4732,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_86
    | ~ spl11_243 ),
    inference(subsumption_resolution,[],[f4731,f234])).

fof(f4731,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_86
    | ~ spl11_243 ),
    inference(subsumption_resolution,[],[f4727,f525])).

fof(f525,plain,
    ( l1_struct_0(sK3)
    | ~ spl11_86 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl11_86
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f4727,plain,
    ( ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl11_243 ),
    inference(resolution,[],[f4507,f175])).

fof(f4507,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl11_243 ),
    inference(avatar_component_clause,[],[f4506])).

fof(f4506,plain,
    ( spl11_243
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_243])])).

fof(f4633,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51
    | spl11_247 ),
    inference(avatar_contradiction_clause,[],[f4632])).

fof(f4632,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4631,f391])).

fof(f4631,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4630,f384])).

fof(f4630,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4629,f377])).

fof(f4629,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4628,f370])).

fof(f4628,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4627,f363])).

fof(f4627,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4626,f356])).

fof(f4626,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4625,f222])).

fof(f4625,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4624,f342])).

fof(f4624,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4623,f216])).

fof(f4623,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4622,f234])).

fof(f4622,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_247 ),
    inference(subsumption_resolution,[],[f4614,f2310])).

fof(f2310,plain,
    ( ! [X3] : v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X3))
    | ~ spl11_0
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f2309,f216])).

fof(f2309,plain,
    ( ! [X3] :
        ( v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X3))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    | ~ spl11_0
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f2299,f234])).

fof(f2299,plain,
    ( ! [X3] :
        ( v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X3))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    | ~ spl11_0
    | ~ spl11_6 ),
    inference(superposition,[],[f2263,f196])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',redefinition_k2_partfun1)).

fof(f2263,plain,
    ( ! [X14] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X14))
    | ~ spl11_0
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f2217,f216])).

fof(f2217,plain,
    ( ! [X14] :
        ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X14))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    | ~ spl11_6 ),
    inference(resolution,[],[f234,f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',dt_k2_partfun1)).

fof(f4614,plain,
    ( ~ v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK2)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_247 ),
    inference(superposition,[],[f4556,f792])).

fof(f792,plain,(
    ! [X6,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k7_relat_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f791])).

fof(f791,plain,(
    ! [X6,X8,X7,X9] :
      ( k2_tmap_1(X6,X7,X8,X9) = k7_relat_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f196,f177])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',d4_tmap_1)).

fof(f4556,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ spl11_247 ),
    inference(avatar_component_clause,[],[f4555])).

fof(f4555,plain,
    ( spl11_247
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_247])])).

fof(f4569,plain,
    ( ~ spl11_247
    | ~ spl11_249
    | spl11_250
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_88
    | ~ spl11_190 ),
    inference(avatar_split_clause,[],[f4550,f2562,f534,f421,f414,f313,f306,f292,f233,f221,f215,f4567,f4561,f4555])).

fof(f4567,plain,
    ( spl11_250
  <=> k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_250])])).

fof(f292,plain,
    ( spl11_22
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f306,plain,
    ( spl11_26
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f313,plain,
    ( spl11_28
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f2562,plain,
    ( spl11_190
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_190])])).

fof(f4550,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_88
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f4549,f422])).

fof(f4549,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ l1_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_56
    | ~ spl11_88
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f4548,f216])).

fof(f4548,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_56
    | ~ spl11_88
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f4547,f222])).

fof(f4547,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_56
    | ~ spl11_88
    | ~ spl11_190 ),
    inference(subsumption_resolution,[],[f4544,f234])).

fof(f4544,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_56
    | ~ spl11_88
    | ~ spl11_190 ),
    inference(resolution,[],[f1200,f2563])).

fof(f2563,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ spl11_190 ),
    inference(avatar_component_clause,[],[f2562])).

fof(f1200,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK2),sK4)
        | k2_tmap_1(X3,sK1,X4,sK2) = sK4
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X3) )
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_56
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f1199,f415])).

fof(f1199,plain,
    ( ! [X4,X3] :
        ( k2_tmap_1(X3,sK1,X4,sK2) = sK4
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK2),sK4)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X3) )
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f1192,f535])).

fof(f1192,plain,
    ( ! [X4,X3] :
        ( k2_tmap_1(X3,sK1,X4,sK2) = sK4
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK2),sK4)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK2))
        | ~ l1_struct_0(sK2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X3) )
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28 ),
    inference(resolution,[],[f725,f176])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f725,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | sK4 = X1
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X1,sK4)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f724,f314])).

fof(f314,plain,
    ( v1_funct_1(sK4)
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f313])).

fof(f724,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X1,sK4)
        | sK4 = X1
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl11_22
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f718,f307])).

fof(f307,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f306])).

fof(f718,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X1,sK4)
        | sK4 = X1
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl11_22 ),
    inference(resolution,[],[f156,f293])).

fof(f293,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f292])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',redefinition_r2_funct_2)).

fof(f4543,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51
    | spl11_241 ),
    inference(avatar_contradiction_clause,[],[f4542])).

fof(f4542,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4541,f391])).

fof(f4541,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4540,f384])).

fof(f4540,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4539,f377])).

fof(f4539,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4538,f370])).

fof(f4538,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4537,f363])).

fof(f4537,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4536,f356])).

fof(f4536,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4535,f222])).

fof(f4535,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4534,f328])).

fof(f4534,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4533,f216])).

fof(f4533,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4532,f234])).

fof(f4532,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_241 ),
    inference(subsumption_resolution,[],[f4524,f2310])).

fof(f4524,plain,
    ( ~ v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK3)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_241 ),
    inference(superposition,[],[f4501,f792])).

fof(f4501,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ spl11_241 ),
    inference(avatar_component_clause,[],[f4500])).

fof(f4500,plain,
    ( spl11_241
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_241])])).

fof(f4514,plain,
    ( ~ spl11_241
    | ~ spl11_243
    | spl11_244
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_86
    | ~ spl11_188 ),
    inference(avatar_split_clause,[],[f4495,f2544,f524,f421,f414,f285,f278,f264,f233,f221,f215,f4512,f4506,f4500])).

fof(f2544,plain,
    ( spl11_188
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_188])])).

fof(f4495,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_86
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f4494,f422])).

fof(f4494,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ l1_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_86
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f4493,f216])).

fof(f4493,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_86
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f4492,f222])).

fof(f4492,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_86
    | ~ spl11_188 ),
    inference(subsumption_resolution,[],[f4489,f234])).

fof(f4489,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_86
    | ~ spl11_188 ),
    inference(resolution,[],[f1124,f2545])).

fof(f2545,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ spl11_188 ),
    inference(avatar_component_clause,[],[f2544])).

fof(f1124,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK3),sK5)
        | k2_tmap_1(X3,sK1,X4,sK3) = sK5
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X3) )
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_86 ),
    inference(subsumption_resolution,[],[f1123,f415])).

fof(f1123,plain,
    ( ! [X4,X3] :
        ( k2_tmap_1(X3,sK1,X4,sK3) = sK5
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK3),sK5)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X3) )
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_86 ),
    inference(subsumption_resolution,[],[f1116,f525])).

fof(f1116,plain,
    ( ! [X4,X3] :
        ( k2_tmap_1(X3,sK1,X4,sK3) = sK5
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK3),sK5)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK3))
        | ~ l1_struct_0(sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X3) )
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(resolution,[],[f723,f176])).

fof(f723,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | sK5 = X0
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f722,f286])).

fof(f722,plain,
    ( ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5)
        | sK5 = X0
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f717,f279])).

fof(f717,plain,
    ( ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5)
        | sK5 = X0
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl11_14 ),
    inference(resolution,[],[f156,f265])).

fof(f2564,plain,
    ( spl11_190
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(avatar_split_clause,[],[f2557,f671,f444,f390,f383,f376,f369,f362,f355,f341,f233,f221,f215,f2562])).

fof(f444,plain,
    ( spl11_64
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f671,plain,
    ( spl11_104
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).

fof(f2557,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2556,f391])).

fof(f2556,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2555,f384])).

fof(f2555,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2554,f377])).

fof(f2554,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2553,f370])).

fof(f2553,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2552,f363])).

fof(f2552,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2551,f356])).

fof(f2551,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_64
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2550,f672])).

fof(f672,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl11_104 ),
    inference(avatar_component_clause,[],[f671])).

fof(f2550,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_64 ),
    inference(subsumption_resolution,[],[f2549,f216])).

fof(f2549,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_64 ),
    inference(subsumption_resolution,[],[f2548,f222])).

fof(f2548,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_36
    | ~ spl11_64 ),
    inference(subsumption_resolution,[],[f2547,f234])).

fof(f2547,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_36
    | ~ spl11_64 ),
    inference(subsumption_resolution,[],[f2525,f342])).

fof(f2525,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_64 ),
    inference(duplicate_literal_removal,[],[f2494])).

fof(f2494,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_64 ),
    inference(superposition,[],[f445,f854])).

fof(f854,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k3_tmap_1(X10,X7,X6,X9,X8) = k2_tmap_1(X6,X7,X8,X9)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f853,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',dt_m1_pre_topc)).

fof(f853,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k3_tmap_1(X10,X7,X6,X9,X8) = k2_tmap_1(X6,X7,X8,X9)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f851,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',cc1_pre_topc)).

fof(f851,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k3_tmap_1(X10,X7,X6,X9,X8) = k2_tmap_1(X6,X7,X8,X9)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f836])).

fof(f836,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( k3_tmap_1(X10,X7,X6,X9,X8) = k2_tmap_1(X6,X7,X8,X9)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X6,X10)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f163,f177])).

fof(f163,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',d5_tmap_1)).

fof(f445,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f444])).

fof(f2546,plain,
    ( spl11_188
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(avatar_split_clause,[],[f2539,f671,f436,f390,f383,f376,f369,f362,f355,f327,f233,f221,f215,f2544])).

fof(f436,plain,
    ( spl11_62
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f2539,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2538,f391])).

fof(f2538,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2537,f384])).

fof(f2537,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2536,f377])).

fof(f2536,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2535,f370])).

fof(f2535,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2534,f363])).

fof(f2534,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_40
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2533,f356])).

fof(f2533,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_62
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2532,f672])).

fof(f2532,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_62 ),
    inference(subsumption_resolution,[],[f2531,f216])).

fof(f2531,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_62 ),
    inference(subsumption_resolution,[],[f2530,f222])).

fof(f2530,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_32
    | ~ spl11_62 ),
    inference(subsumption_resolution,[],[f2529,f234])).

fof(f2529,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_32
    | ~ spl11_62 ),
    inference(subsumption_resolution,[],[f2526,f328])).

fof(f2526,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_62 ),
    inference(duplicate_literal_removal,[],[f2493])).

fof(f2493,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_62 ),
    inference(superposition,[],[f437,f854])).

fof(f437,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl11_62 ),
    inference(avatar_component_clause,[],[f436])).

fof(f2202,plain,
    ( spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | spl11_35
    | ~ spl11_36
    | spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51 ),
    inference(avatar_contradiction_clause,[],[f2201])).

fof(f2201,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2200,f370])).

fof(f2200,plain,
    ( v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2199,f363])).

fof(f2199,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2198,f356])).

fof(f2198,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2197,f314])).

fof(f2197,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2196,f307])).

fof(f2196,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2195,f293])).

fof(f2195,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2194,f286])).

fof(f2194,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2193,f279])).

fof(f2193,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f2191,f265])).

fof(f2191,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_7
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(resolution,[],[f237,f1058])).

fof(f1058,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1057,f391])).

fof(f1057,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1056,f384])).

fof(f1056,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f1055,f377])).

fof(f1055,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f1054,f349])).

fof(f1054,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f1053,f342])).

fof(f1053,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f1052,f335])).

fof(f1052,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f1030,f328])).

fof(f1030,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30 ),
    inference(superposition,[],[f166,f321])).

fof(f166,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',dt_k10_tmap_1)).

fof(f237,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl11_7
  <=> ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1580,plain,
    ( spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | spl11_35
    | ~ spl11_36
    | spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51 ),
    inference(avatar_contradiction_clause,[],[f1579])).

fof(f1579,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1578,f370])).

fof(f1578,plain,
    ( v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1577,f363])).

fof(f1577,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1576,f356])).

fof(f1576,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1575,f314])).

fof(f1575,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1574,f307])).

fof(f1574,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1573,f293])).

fof(f1573,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1572,f286])).

fof(f1572,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1571,f279])).

fof(f1571,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_14
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1569,f265])).

fof(f1569,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_3
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(resolution,[],[f1016,f225])).

fof(f225,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl11_3
  <=> ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1016,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f1015,f391])).

fof(f1015,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1014,f384])).

fof(f1014,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f1013,f377])).

fof(f1013,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f1012,f349])).

fof(f1012,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f1011,f342])).

fof(f1011,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f1010,f335])).

fof(f1010,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f1005,f328])).

fof(f1005,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_30 ),
    inference(superposition,[],[f165,f321])).

fof(f165,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f923,plain,
    ( spl11_1
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | spl11_35
    | ~ spl11_36
    | spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | spl11_51 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_28
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_40
    | ~ spl11_42
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_48
    | ~ spl11_51 ),
    inference(unit_resulting_resolution,[],[f391,f384,f377,f370,f363,f356,f349,f314,f335,f286,f342,f328,f307,f219,f293,f279,f265,f164])).

fof(f164,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f219,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl11_1
  <=> ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f673,plain,
    ( spl11_104
    | ~ spl11_30
    | ~ spl11_32
    | spl11_35
    | ~ spl11_36
    | spl11_39
    | ~ spl11_46
    | spl11_51 ),
    inference(avatar_split_clause,[],[f666,f390,f376,f348,f341,f334,f327,f320,f671])).

fof(f666,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f665,f391])).

fof(f665,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f664,f377])).

fof(f664,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f663,f349])).

fof(f663,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35
    | ~ spl11_36 ),
    inference(subsumption_resolution,[],[f662,f342])).

fof(f662,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_30
    | ~ spl11_32
    | ~ spl11_35 ),
    inference(subsumption_resolution,[],[f661,f335])).

fof(f661,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_30
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f658,f328])).

fof(f658,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_30 ),
    inference(superposition,[],[f191,f321])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',dt_k1_tsep_1)).

fof(f536,plain,
    ( spl11_88
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f529,f464,f534])).

fof(f464,plain,
    ( spl11_68
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f529,plain,
    ( l1_struct_0(sK2)
    | ~ spl11_68 ),
    inference(resolution,[],[f465,f200])).

fof(f200,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',dt_l1_pre_topc)).

fof(f465,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f464])).

fof(f526,plain,
    ( spl11_86
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f519,f456,f524])).

fof(f456,plain,
    ( spl11_66
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f519,plain,
    ( l1_struct_0(sK3)
    | ~ spl11_66 ),
    inference(resolution,[],[f457,f200])).

fof(f457,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f456])).

fof(f466,plain,
    ( spl11_68
    | ~ spl11_36
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f459,f376,f341,f464])).

fof(f459,plain,
    ( l1_pre_topc(sK2)
    | ~ spl11_36
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f448,f377])).

fof(f448,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl11_36 ),
    inference(resolution,[],[f194,f342])).

fof(f458,plain,
    ( spl11_66
    | ~ spl11_32
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f451,f376,f327,f456])).

fof(f451,plain,
    ( l1_pre_topc(sK3)
    | ~ spl11_32
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f447,f377])).

fof(f447,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl11_32 ),
    inference(resolution,[],[f194,f328])).

fof(f446,plain,
    ( spl11_64
    | ~ spl11_12
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f439,f320,f257,f444])).

fof(f257,plain,
    ( spl11_12
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f439,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl11_12
    | ~ spl11_30 ),
    inference(forward_demodulation,[],[f258,f321])).

fof(f258,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f257])).

fof(f438,plain,
    ( spl11_62
    | ~ spl11_10
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f431,f320,f250,f436])).

fof(f250,plain,
    ( spl11_10
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f431,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl11_10
    | ~ spl11_30 ),
    inference(forward_demodulation,[],[f251,f321])).

fof(f251,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f250])).

fof(f423,plain,
    ( spl11_58
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f408,f376,f421])).

fof(f408,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_46 ),
    inference(resolution,[],[f200,f377])).

fof(f416,plain,
    ( spl11_56
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f407,f355,f414])).

fof(f407,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_40 ),
    inference(resolution,[],[f200,f356])).

fof(f392,plain,(
    ~ spl11_51 ),
    inference(avatar_split_clause,[],[f120,f390])).

fof(f120,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & r4_tsep_1(sK0,sK2,sK3)
    & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & k1_tsep_1(sK0,sK2,sK3) = sK0
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f49,f105,f104,f103,f102,f101,f100])).

fof(f100,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r4_tsep_1(X0,X2,X3)
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(sK0,X2,X3) = sK0
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

fof(f101,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK1,X2,X3,X4,X5),X0,sK1)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK1))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK1,X2,X3,X4,X5)) )
                        & r4_tsep_1(X0,X2,X3)
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X4)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                        & v5_pre_topc(X5,X3,sK1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v5_pre_topc(X4,X2,sK1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & k1_tsep_1(X0,X2,X3) = X0
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r4_tsep_1(X0,X2,X3)
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & k1_tsep_1(X0,X2,X3) = X0
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK2,X3,X4,X5),X0,X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5)) )
                    & r4_tsep_1(X0,sK2,X3)
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),X3,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),sK2,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X4)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK2,X1)
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & k1_tsep_1(X0,sK2,X3) = X0
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r4_tsep_1(X0,X2,X3)
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & k1_tsep_1(X0,X2,X3) = X0
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK3,X4,X5),X0,X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5)) )
                & r4_tsep_1(X0,X2,sK3)
                & r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),sK3,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),X2,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X4)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK3,X1)
                & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & k1_tsep_1(X0,X2,sK3) = X0
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r4_tsep_1(X0,X2,X3)
              & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(X5,X3,X1)
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(X4,X2,X1)
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK4,X5),X0,X1)
              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK4,X5),u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK4,X5)) )
            & r4_tsep_1(X0,X2,X3)
            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),X5)
            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),sK4)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK4,X2,X1)
        & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r4_tsep_1(X0,X2,X3)
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK5),X0,X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK5),u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5)) )
        & r4_tsep_1(X0,X2,X3)
        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),sK5)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),X4)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK5,X3,X1)
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(X4,X2,X1)
                            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(X5,X3,X1)
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ( r4_tsep_1(X0,X2,X3)
                                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t151_tmap_1.p',t151_tmap_1)).

fof(f385,plain,(
    spl11_48 ),
    inference(avatar_split_clause,[],[f121,f383])).

fof(f121,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f378,plain,(
    spl11_46 ),
    inference(avatar_split_clause,[],[f122,f376])).

fof(f122,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f371,plain,(
    ~ spl11_45 ),
    inference(avatar_split_clause,[],[f123,f369])).

fof(f123,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f364,plain,(
    spl11_42 ),
    inference(avatar_split_clause,[],[f124,f362])).

fof(f124,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f357,plain,(
    spl11_40 ),
    inference(avatar_split_clause,[],[f125,f355])).

fof(f125,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f350,plain,(
    ~ spl11_39 ),
    inference(avatar_split_clause,[],[f126,f348])).

fof(f126,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f106])).

fof(f343,plain,(
    spl11_36 ),
    inference(avatar_split_clause,[],[f127,f341])).

fof(f127,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f336,plain,(
    ~ spl11_35 ),
    inference(avatar_split_clause,[],[f128,f334])).

fof(f128,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f106])).

fof(f329,plain,(
    spl11_32 ),
    inference(avatar_split_clause,[],[f129,f327])).

fof(f129,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f322,plain,(
    spl11_30 ),
    inference(avatar_split_clause,[],[f130,f320])).

fof(f130,plain,(
    k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f106])).

fof(f315,plain,(
    spl11_28 ),
    inference(avatar_split_clause,[],[f131,f313])).

fof(f131,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f106])).

fof(f308,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f132,f306])).

fof(f132,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f106])).

fof(f301,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f133,f299])).

fof(f299,plain,
    ( spl11_24
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f133,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f294,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f134,f292])).

fof(f134,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f106])).

fof(f287,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f135,f285])).

fof(f135,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f106])).

fof(f280,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f136,f278])).

fof(f136,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f106])).

fof(f273,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f137,f271])).

fof(f137,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f266,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f138,f264])).

fof(f138,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f106])).

fof(f259,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f139,f257])).

fof(f139,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f106])).

fof(f252,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f140,f250])).

fof(f140,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f106])).

fof(f245,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f141,f243])).

fof(f141,plain,(
    r4_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f106])).

fof(f238,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f142,f236,f230,f224,f218])).

fof(f142,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f106])).
%------------------------------------------------------------------------------

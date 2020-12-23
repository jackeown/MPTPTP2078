%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t152_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:10 EDT 2019

% Result     : Theorem 16.76s
% Output     : Refutation 16.76s
% Verified   : 
% Statistics : Number of formulae       :  409 (1158 expanded)
%              Number of leaves         :   71 ( 522 expanded)
%              Depth                    :   34
%              Number of atoms          : 3907 (13823 expanded)
%              Number of equality atoms :   78 ( 532 expanded)
%              Maximal formula depth    :   31 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5809,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f245,f252,f259,f266,f273,f280,f287,f294,f301,f308,f315,f322,f329,f336,f343,f350,f357,f364,f371,f378,f385,f392,f399,f406,f430,f437,f452,f460,f472,f480,f517,f548,f685,f907,f1596,f2268,f2622,f2640,f4491,f4520,f4546,f4610,f4714,f4810,f5806,f5807,f5808])).

fof(f5808,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(theory_axiom,[])).

fof(f5807,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v5_pre_topc(sK4,sK2,sK1) ),
    introduced(theory_axiom,[])).

fof(f5806,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_90
    | spl12_247 ),
    inference(avatar_contradiction_clause,[],[f5805])).

fof(f5805,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_90
    | ~ spl12_247 ),
    inference(subsumption_resolution,[],[f5804,f436])).

fof(f436,plain,
    ( l1_struct_0(sK0)
    | ~ spl12_60 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl12_60
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_60])])).

fof(f5804,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_58
    | ~ spl12_90
    | ~ spl12_247 ),
    inference(subsumption_resolution,[],[f5803,f429])).

fof(f429,plain,
    ( l1_struct_0(sK1)
    | ~ spl12_58 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl12_58
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f5803,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_90
    | ~ spl12_247 ),
    inference(subsumption_resolution,[],[f5802,f223])).

fof(f223,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl12_0
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f5802,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_90
    | ~ spl12_247 ),
    inference(subsumption_resolution,[],[f5801,f229])).

fof(f229,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl12_2
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f5801,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_6
    | ~ spl12_90
    | ~ spl12_247 ),
    inference(subsumption_resolution,[],[f5800,f241])).

fof(f241,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl12_6
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f5800,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_90
    | ~ spl12_247 ),
    inference(subsumption_resolution,[],[f5796,f547])).

fof(f547,plain,
    ( l1_struct_0(sK2)
    | ~ spl12_90 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl12_90
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_90])])).

fof(f5796,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_247 ),
    inference(resolution,[],[f4539,f185])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
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
    inference(flattening,[],[f80])).

fof(f80,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',dt_k2_tmap_1)).

fof(f4539,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_247 ),
    inference(avatar_component_clause,[],[f4538])).

fof(f4538,plain,
    ( spl12_247
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_247])])).

fof(f4810,plain,
    ( ~ spl12_247
    | ~ spl12_255
    | ~ spl12_257
    | ~ spl12_0
    | ~ spl12_2
    | spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_32
    | spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(avatar_split_clause,[],[f4797,f4529,f4489,f404,f397,f390,f383,f376,f369,f362,f355,f348,f341,f334,f327,f292,f285,f278,f271,f264,f240,f237,f228,f222,f4808,f4802,f4538])).

fof(f4802,plain,
    ( spl12_255
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_255])])).

fof(f4808,plain,
    ( spl12_257
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_257])])).

fof(f237,plain,
    ( spl12_5
  <=> ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f264,plain,
    ( spl12_12
  <=> k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f271,plain,
    ( spl12_14
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f278,plain,
    ( spl12_16
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f285,plain,
    ( spl12_18
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f292,plain,
    ( spl12_20
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f327,plain,
    ( spl12_30
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f334,plain,
    ( spl12_32
  <=> v1_borsuk_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f341,plain,
    ( spl12_35
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).

fof(f348,plain,
    ( spl12_36
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f355,plain,
    ( spl12_38
  <=> v1_borsuk_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).

fof(f362,plain,
    ( spl12_41
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).

fof(f369,plain,
    ( spl12_42
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f376,plain,
    ( spl12_44
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f383,plain,
    ( spl12_47
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f390,plain,
    ( spl12_48
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f397,plain,
    ( spl12_50
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f404,plain,
    ( spl12_53
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_53])])).

fof(f4489,plain,
    ( spl12_242
  <=> k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_242])])).

fof(f4529,plain,
    ( spl12_244
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_244])])).

fof(f4797,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4796,f293])).

fof(f293,plain,
    ( v1_funct_1(sK5)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f292])).

fof(f4796,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_18
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(forward_demodulation,[],[f4795,f4490])).

fof(f4490,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ spl12_242 ),
    inference(avatar_component_clause,[],[f4489])).

fof(f4795,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_18
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4794,f286])).

fof(f286,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f285])).

fof(f4794,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(forward_demodulation,[],[f4793,f4490])).

fof(f4793,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4792,f279])).

fof(f279,plain,
    ( v5_pre_topc(sK5,sK3,sK1)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f278])).

fof(f4792,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(forward_demodulation,[],[f4791,f4490])).

fof(f4791,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4790,f384])).

fof(f384,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl12_47 ),
    inference(avatar_component_clause,[],[f383])).

fof(f4790,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4789,f377])).

fof(f377,plain,
    ( v2_pre_topc(sK1)
    | ~ spl12_44 ),
    inference(avatar_component_clause,[],[f376])).

fof(f4789,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4788,f370])).

fof(f370,plain,
    ( l1_pre_topc(sK1)
    | ~ spl12_42 ),
    inference(avatar_component_clause,[],[f369])).

fof(f4788,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK2,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4787,f223])).

fof(f4787,plain,
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
    | ~ spl12_2
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4786,f229])).

fof(f4786,plain,
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
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4785,f241])).

fof(f4785,plain,
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
    | ~ spl12_5
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4784,f238])).

fof(f238,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f237])).

fof(f4784,plain,
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
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242
    | ~ spl12_244 ),
    inference(subsumption_resolution,[],[f4783,f4530])).

fof(f4530,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ spl12_244 ),
    inference(avatar_component_clause,[],[f4529])).

fof(f4783,plain,
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
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242 ),
    inference(subsumption_resolution,[],[f4730,f272])).

fof(f272,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f271])).

fof(f4730,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_242 ),
    inference(superposition,[],[f1120,f4490])).

fof(f1120,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1119,f405])).

fof(f405,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl12_53 ),
    inference(avatar_component_clause,[],[f404])).

fof(f1119,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50 ),
    inference(subsumption_resolution,[],[f1118,f398])).

fof(f398,plain,
    ( v2_pre_topc(sK0)
    | ~ spl12_50 ),
    inference(avatar_component_clause,[],[f397])).

fof(f1118,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f1117,f391])).

fof(f391,plain,
    ( l1_pre_topc(sK0)
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f390])).

fof(f1117,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38
    | ~ spl12_41 ),
    inference(subsumption_resolution,[],[f1116,f363])).

fof(f363,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl12_41 ),
    inference(avatar_component_clause,[],[f362])).

fof(f1116,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_38 ),
    inference(subsumption_resolution,[],[f1115,f356])).

fof(f356,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ spl12_38 ),
    inference(avatar_component_clause,[],[f355])).

fof(f1115,plain,
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
        | ~ v1_borsuk_1(sK2,sK0)
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f1114,f349])).

fof(f349,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f348])).

fof(f1114,plain,
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
        | ~ v1_borsuk_1(sK2,sK0)
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f1113,f342])).

fof(f342,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl12_35 ),
    inference(avatar_component_clause,[],[f341])).

fof(f1113,plain,
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
        | ~ v1_borsuk_1(sK2,sK0)
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f1112,f335])).

fof(f335,plain,
    ( v1_borsuk_1(sK3,sK0)
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f334])).

fof(f1112,plain,
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
        | ~ v1_borsuk_1(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_borsuk_1(sK2,sK0)
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
    | ~ spl12_12
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f1111,f328])).

fof(f328,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f327])).

fof(f1111,plain,
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
        | ~ v1_borsuk_1(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_borsuk_1(sK2,sK0)
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
    | ~ spl12_12 ),
    inference(trivial_inequality_removal,[],[f1106])).

fof(f1106,plain,
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
        | v5_pre_topc(X1,sK0,X0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_borsuk_1(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ v1_borsuk_1(sK2,sK0)
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
    | ~ spl12_12 ),
    inference(superposition,[],[f171,f265])).

fof(f265,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f264])).

fof(f171,plain,(
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
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_pre_topc(X4,X0)
      | ~ v1_borsuk_1(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_borsuk_1(X3,X0)
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
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
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
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(flattening,[],[f108])).

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
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
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
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | ~ v1_borsuk_1(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_borsuk_1(X3,X0)
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
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
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
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',t133_tmap_1)).

fof(f4714,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_80
    | spl12_241 ),
    inference(avatar_contradiction_clause,[],[f4713])).

fof(f4713,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_80
    | ~ spl12_241 ),
    inference(subsumption_resolution,[],[f4712,f436])).

fof(f4712,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_58
    | ~ spl12_80
    | ~ spl12_241 ),
    inference(subsumption_resolution,[],[f4711,f429])).

fof(f4711,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_80
    | ~ spl12_241 ),
    inference(subsumption_resolution,[],[f4710,f223])).

fof(f4710,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_80
    | ~ spl12_241 ),
    inference(subsumption_resolution,[],[f4709,f229])).

fof(f4709,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_6
    | ~ spl12_80
    | ~ spl12_241 ),
    inference(subsumption_resolution,[],[f4708,f241])).

fof(f4708,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_80
    | ~ spl12_241 ),
    inference(subsumption_resolution,[],[f4704,f516])).

fof(f516,plain,
    ( l1_struct_0(sK3)
    | ~ spl12_80 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl12_80
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_80])])).

fof(f4704,plain,
    ( ~ l1_struct_0(sK3)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl12_241 ),
    inference(resolution,[],[f4484,f185])).

fof(f4484,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl12_241 ),
    inference(avatar_component_clause,[],[f4483])).

fof(f4483,plain,
    ( spl12_241
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_241])])).

fof(f4610,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53
    | spl12_245 ),
    inference(avatar_contradiction_clause,[],[f4609])).

fof(f4609,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4608,f405])).

fof(f4608,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4607,f398])).

fof(f4607,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4606,f391])).

fof(f4606,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4605,f384])).

fof(f4605,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4604,f377])).

fof(f4604,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4603,f370])).

fof(f4603,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4602,f229])).

fof(f4602,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4601,f349])).

fof(f4601,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4600,f223])).

fof(f4600,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4599,f241])).

fof(f4599,plain,
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
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_245 ),
    inference(subsumption_resolution,[],[f4591,f2377])).

fof(f2377,plain,
    ( ! [X3] : v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X3))
    | ~ spl12_0
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f2376,f223])).

fof(f2376,plain,
    ( ! [X3] :
        ( v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X3))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    | ~ spl12_0
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f2366,f241])).

fof(f2366,plain,
    ( ! [X3] :
        ( v1_funct_1(k7_relat_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X3))
        | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    | ~ spl12_0
    | ~ spl12_6 ),
    inference(superposition,[],[f2330,f203])).

fof(f203,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',redefinition_k2_partfun1)).

fof(f2330,plain,
    ( ! [X15] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X15))
    | ~ spl12_0
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f2284,f223])).

fof(f2284,plain,
    ( ! [X15] :
        ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X15))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    | ~ spl12_6 ),
    inference(resolution,[],[f241,f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',dt_k2_partfun1)).

fof(f4591,plain,
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
    | ~ spl12_245 ),
    inference(superposition,[],[f4533,f798])).

fof(f798,plain,(
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
    inference(duplicate_literal_removal,[],[f797])).

fof(f797,plain,(
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
    inference(superposition,[],[f203,f173])).

fof(f173,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f68,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',d4_tmap_1)).

fof(f4533,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ spl12_245 ),
    inference(avatar_component_clause,[],[f4532])).

fof(f4532,plain,
    ( spl12_245
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_245])])).

fof(f4546,plain,
    ( ~ spl12_245
    | ~ spl12_247
    | spl12_248
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_90
    | ~ spl12_190 ),
    inference(avatar_split_clause,[],[f4527,f2638,f546,f435,f428,f320,f313,f299,f240,f228,f222,f4544,f4538,f4532])).

fof(f4544,plain,
    ( spl12_248
  <=> k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_248])])).

fof(f299,plain,
    ( spl12_22
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f313,plain,
    ( spl12_26
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f320,plain,
    ( spl12_28
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f2638,plain,
    ( spl12_190
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_190])])).

fof(f4527,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_90
    | ~ spl12_190 ),
    inference(subsumption_resolution,[],[f4526,f436])).

fof(f4526,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ l1_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_58
    | ~ spl12_90
    | ~ spl12_190 ),
    inference(subsumption_resolution,[],[f4525,f223])).

fof(f4525,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_58
    | ~ spl12_90
    | ~ spl12_190 ),
    inference(subsumption_resolution,[],[f4524,f229])).

fof(f4524,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl12_6
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_58
    | ~ spl12_90
    | ~ spl12_190 ),
    inference(subsumption_resolution,[],[f4521,f241])).

fof(f4521,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_58
    | ~ spl12_90
    | ~ spl12_190 ),
    inference(resolution,[],[f1206,f2639])).

fof(f2639,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ spl12_190 ),
    inference(avatar_component_clause,[],[f2638])).

fof(f1206,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK2),sK4)
        | k2_tmap_1(X3,sK1,X4,sK2) = sK4
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X3) )
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_58
    | ~ spl12_90 ),
    inference(subsumption_resolution,[],[f1205,f429])).

fof(f1205,plain,
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
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_90 ),
    inference(subsumption_resolution,[],[f1198,f547])).

fof(f1198,plain,
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
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28 ),
    inference(resolution,[],[f737,f186])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f737,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | sK4 = X1
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X1,sK4)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f736,f321])).

fof(f321,plain,
    ( v1_funct_1(sK4)
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f320])).

fof(f736,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X1,sK4)
        | sK4 = X1
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl12_22
    | ~ spl12_26 ),
    inference(subsumption_resolution,[],[f730,f314])).

fof(f314,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f313])).

fof(f730,plain,
    ( ! [X1] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X1,sK4)
        | sK4 = X1
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(X1) )
    | ~ spl12_22 ),
    inference(resolution,[],[f146,f300])).

fof(f300,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f299])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',redefinition_r2_funct_2)).

fof(f4520,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53
    | spl12_239 ),
    inference(avatar_contradiction_clause,[],[f4519])).

fof(f4519,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4518,f405])).

fof(f4518,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4517,f398])).

fof(f4517,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4516,f391])).

fof(f4516,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4515,f384])).

fof(f4515,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4514,f377])).

fof(f4514,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4513,f370])).

fof(f4513,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4512,f229])).

fof(f4512,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4511,f328])).

fof(f4511,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4510,f223])).

fof(f4510,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4509,f241])).

fof(f4509,plain,
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
    | ~ spl12_0
    | ~ spl12_6
    | ~ spl12_239 ),
    inference(subsumption_resolution,[],[f4501,f2377])).

fof(f4501,plain,
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
    | ~ spl12_239 ),
    inference(superposition,[],[f4478,f798])).

fof(f4478,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ spl12_239 ),
    inference(avatar_component_clause,[],[f4477])).

fof(f4477,plain,
    ( spl12_239
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_239])])).

fof(f4491,plain,
    ( ~ spl12_239
    | ~ spl12_241
    | spl12_242
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_80
    | ~ spl12_188 ),
    inference(avatar_split_clause,[],[f4472,f2620,f515,f435,f428,f292,f285,f271,f240,f228,f222,f4489,f4483,f4477])).

fof(f2620,plain,
    ( spl12_188
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_188])])).

fof(f4472,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_58
    | ~ spl12_60
    | ~ spl12_80
    | ~ spl12_188 ),
    inference(subsumption_resolution,[],[f4471,f436])).

fof(f4471,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ l1_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_58
    | ~ spl12_80
    | ~ spl12_188 ),
    inference(subsumption_resolution,[],[f4470,f223])).

fof(f4470,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_58
    | ~ spl12_80
    | ~ spl12_188 ),
    inference(subsumption_resolution,[],[f4469,f229])).

fof(f4469,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl12_6
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_58
    | ~ spl12_80
    | ~ spl12_188 ),
    inference(subsumption_resolution,[],[f4466,f241])).

fof(f4466,plain,
    ( k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ l1_struct_0(sK0)
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_58
    | ~ spl12_80
    | ~ spl12_188 ),
    inference(resolution,[],[f1139,f2621])).

fof(f2621,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ spl12_188 ),
    inference(avatar_component_clause,[],[f2620])).

fof(f1139,plain,
    ( ! [X4,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(X3,sK1,X4,sK3),sK5)
        | k2_tmap_1(X3,sK1,X4,sK3) = sK5
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,sK3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X3) )
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_58
    | ~ spl12_80 ),
    inference(subsumption_resolution,[],[f1138,f429])).

fof(f1138,plain,
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
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_80 ),
    inference(subsumption_resolution,[],[f1131,f516])).

fof(f1131,plain,
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
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20 ),
    inference(resolution,[],[f735,f186])).

fof(f735,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | sK5 = X0
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f734,f293])).

fof(f734,plain,
    ( ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5)
        | sK5 = X0
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl12_14
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f729,f286])).

fof(f729,plain,
    ( ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X0,sK5)
        | sK5 = X0
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl12_14 ),
    inference(resolution,[],[f146,f272])).

fof(f2640,plain,
    ( spl12_190
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(avatar_split_clause,[],[f2633,f683,f458,f404,f397,f390,f383,f376,f369,f348,f240,f228,f222,f2638])).

fof(f458,plain,
    ( spl12_66
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_66])])).

fof(f683,plain,
    ( spl12_106
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_106])])).

fof(f2633,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2632,f405])).

fof(f2632,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2631,f398])).

fof(f2631,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2630,f391])).

fof(f2630,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2629,f384])).

fof(f2629,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2628,f377])).

fof(f2628,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_42
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2627,f370])).

fof(f2627,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_66
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2626,f684])).

fof(f684,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl12_106 ),
    inference(avatar_component_clause,[],[f683])).

fof(f2626,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_66 ),
    inference(subsumption_resolution,[],[f2625,f223])).

fof(f2625,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2),sK4)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_66 ),
    inference(subsumption_resolution,[],[f2624,f229])).

fof(f2624,plain,
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
    | ~ spl12_6
    | ~ spl12_36
    | ~ spl12_66 ),
    inference(subsumption_resolution,[],[f2623,f241])).

fof(f2623,plain,
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
    | ~ spl12_36
    | ~ spl12_66 ),
    inference(subsumption_resolution,[],[f2601,f349])).

fof(f2601,plain,
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
    | ~ spl12_66 ),
    inference(duplicate_literal_removal,[],[f2570])).

fof(f2570,plain,
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
    | ~ spl12_66 ),
    inference(superposition,[],[f459,f860])).

fof(f860,plain,(
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
    inference(subsumption_resolution,[],[f859,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',cc1_pre_topc)).

fof(f859,plain,(
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
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f857,f201])).

fof(f201,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',dt_m1_pre_topc)).

fof(f857,plain,(
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
    inference(duplicate_literal_removal,[],[f842])).

fof(f842,plain,(
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
    inference(superposition,[],[f153,f173])).

fof(f153,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',d5_tmap_1)).

fof(f459,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl12_66 ),
    inference(avatar_component_clause,[],[f458])).

fof(f2622,plain,
    ( spl12_188
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(avatar_split_clause,[],[f2615,f683,f450,f404,f397,f390,f383,f376,f369,f327,f240,f228,f222,f2620])).

fof(f450,plain,
    ( spl12_64
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_64])])).

fof(f2615,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2614,f405])).

fof(f2614,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2613,f398])).

fof(f2613,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2612,f391])).

fof(f2612,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2611,f384])).

fof(f2611,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2610,f377])).

fof(f2610,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_42
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2609,f370])).

fof(f2609,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_64
    | ~ spl12_106 ),
    inference(subsumption_resolution,[],[f2608,f684])).

fof(f2608,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_64 ),
    inference(subsumption_resolution,[],[f2607,f223])).

fof(f2607,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3),sK5)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_64 ),
    inference(subsumption_resolution,[],[f2606,f229])).

fof(f2606,plain,
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
    | ~ spl12_6
    | ~ spl12_30
    | ~ spl12_64 ),
    inference(subsumption_resolution,[],[f2605,f241])).

fof(f2605,plain,
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
    | ~ spl12_30
    | ~ spl12_64 ),
    inference(subsumption_resolution,[],[f2602,f328])).

fof(f2602,plain,
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
    | ~ spl12_64 ),
    inference(duplicate_literal_removal,[],[f2569])).

fof(f2569,plain,
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
    | ~ spl12_64 ),
    inference(superposition,[],[f451,f860])).

fof(f451,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl12_64 ),
    inference(avatar_component_clause,[],[f450])).

fof(f2268,plain,
    ( spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | spl12_35
    | ~ spl12_36
    | spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53 ),
    inference(avatar_contradiction_clause,[],[f2267])).

fof(f2267,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2266,f384])).

fof(f2266,plain,
    ( v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2265,f377])).

fof(f2265,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2264,f370])).

fof(f2264,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2263,f321])).

fof(f2263,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2262,f314])).

fof(f2262,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2261,f300])).

fof(f2261,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2260,f293])).

fof(f2260,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2259,f286])).

fof(f2259,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f2257,f272])).

fof(f2257,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(resolution,[],[f244,f1105])).

fof(f1105,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1104,f405])).

fof(f1104,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50 ),
    inference(subsumption_resolution,[],[f1103,f398])).

fof(f1103,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f1102,f391])).

fof(f1102,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41 ),
    inference(subsumption_resolution,[],[f1101,f363])).

fof(f1101,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f1100,f349])).

fof(f1100,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f1099,f342])).

fof(f1099,plain,
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
    | ~ spl12_12
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f1077,f328])).

fof(f1077,plain,
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
    | ~ spl12_12 ),
    inference(superposition,[],[f156,f265])).

fof(f156,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',dt_k10_tmap_1)).

fof(f244,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl12_7
  <=> ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f1596,plain,
    ( spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | spl12_35
    | ~ spl12_36
    | spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53 ),
    inference(avatar_contradiction_clause,[],[f1595])).

fof(f1595,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1594,f384])).

fof(f1594,plain,
    ( v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1593,f377])).

fof(f1593,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1592,f370])).

fof(f1592,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1591,f321])).

fof(f1591,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1590,f314])).

fof(f1590,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1589,f300])).

fof(f1589,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1588,f293])).

fof(f1588,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1587,f286])).

fof(f1587,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1585,f272])).

fof(f1585,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(resolution,[],[f1066,f232])).

fof(f232,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl12_3
  <=> ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f1066,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f1065,f405])).

fof(f1065,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_50 ),
    inference(subsumption_resolution,[],[f1064,f398])).

fof(f1064,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f1063,f391])).

fof(f1063,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41 ),
    inference(subsumption_resolution,[],[f1062,f363])).

fof(f1062,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f1061,f349])).

fof(f1061,plain,
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
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f1060,f342])).

fof(f1060,plain,
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
    | ~ spl12_12
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f1055,f328])).

fof(f1055,plain,
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
    | ~ spl12_12 ),
    inference(superposition,[],[f155,f265])).

fof(f155,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f907,plain,
    ( spl12_1
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | spl12_35
    | ~ spl12_36
    | spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | spl12_53 ),
    inference(avatar_contradiction_clause,[],[f897])).

fof(f897,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_14
    | ~ spl12_18
    | ~ spl12_20
    | ~ spl12_22
    | ~ spl12_26
    | ~ spl12_28
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_42
    | ~ spl12_44
    | ~ spl12_47
    | ~ spl12_48
    | ~ spl12_50
    | ~ spl12_53 ),
    inference(unit_resulting_resolution,[],[f405,f398,f391,f384,f377,f370,f363,f321,f342,f293,f349,f328,f314,f226,f300,f286,f272,f154])).

fof(f154,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f226,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl12_1
  <=> ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f685,plain,
    ( spl12_106
    | ~ spl12_12
    | ~ spl12_30
    | spl12_35
    | ~ spl12_36
    | spl12_41
    | ~ spl12_48
    | spl12_53 ),
    inference(avatar_split_clause,[],[f678,f404,f390,f362,f348,f341,f327,f264,f683])).

fof(f678,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48
    | ~ spl12_53 ),
    inference(subsumption_resolution,[],[f677,f405])).

fof(f677,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f676,f391])).

fof(f676,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36
    | ~ spl12_41 ),
    inference(subsumption_resolution,[],[f675,f363])).

fof(f675,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f674,f349])).

fof(f674,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_12
    | ~ spl12_30
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f673,f342])).

fof(f673,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_12
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f670,f328])).

fof(f670,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_12 ),
    inference(superposition,[],[f176,f265])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',dt_k1_tsep_1)).

fof(f548,plain,
    ( spl12_90
    | ~ spl12_70 ),
    inference(avatar_split_clause,[],[f541,f478,f546])).

fof(f478,plain,
    ( spl12_70
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).

fof(f541,plain,
    ( l1_struct_0(sK2)
    | ~ spl12_70 ),
    inference(resolution,[],[f479,f209])).

fof(f209,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',dt_l1_pre_topc)).

fof(f479,plain,
    ( l1_pre_topc(sK2)
    | ~ spl12_70 ),
    inference(avatar_component_clause,[],[f478])).

fof(f517,plain,
    ( spl12_80
    | ~ spl12_68 ),
    inference(avatar_split_clause,[],[f510,f470,f515])).

fof(f470,plain,
    ( spl12_68
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).

fof(f510,plain,
    ( l1_struct_0(sK3)
    | ~ spl12_68 ),
    inference(resolution,[],[f471,f209])).

fof(f471,plain,
    ( l1_pre_topc(sK3)
    | ~ spl12_68 ),
    inference(avatar_component_clause,[],[f470])).

fof(f480,plain,
    ( spl12_70
    | ~ spl12_36
    | ~ spl12_48 ),
    inference(avatar_split_clause,[],[f473,f390,f348,f478])).

fof(f473,plain,
    ( l1_pre_topc(sK2)
    | ~ spl12_36
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f462,f391])).

fof(f462,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl12_36 ),
    inference(resolution,[],[f201,f349])).

fof(f472,plain,
    ( spl12_68
    | ~ spl12_30
    | ~ spl12_48 ),
    inference(avatar_split_clause,[],[f465,f390,f327,f470])).

fof(f465,plain,
    ( l1_pre_topc(sK3)
    | ~ spl12_30
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f461,f391])).

fof(f461,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl12_30 ),
    inference(resolution,[],[f201,f328])).

fof(f460,plain,
    ( spl12_66
    | ~ spl12_10
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f453,f264,f257,f458])).

fof(f257,plain,
    ( spl12_10
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f453,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl12_10
    | ~ spl12_12 ),
    inference(forward_demodulation,[],[f258,f265])).

fof(f258,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f257])).

fof(f452,plain,
    ( spl12_64
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f445,f264,f250,f450])).

fof(f250,plain,
    ( spl12_8
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f445,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(forward_demodulation,[],[f251,f265])).

fof(f251,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f250])).

fof(f437,plain,
    ( spl12_60
    | ~ spl12_48 ),
    inference(avatar_split_clause,[],[f422,f390,f435])).

fof(f422,plain,
    ( l1_struct_0(sK0)
    | ~ spl12_48 ),
    inference(resolution,[],[f209,f391])).

fof(f430,plain,
    ( spl12_58
    | ~ spl12_42 ),
    inference(avatar_split_clause,[],[f421,f369,f428])).

fof(f421,plain,
    ( l1_struct_0(sK1)
    | ~ spl12_42 ),
    inference(resolution,[],[f209,f370])).

fof(f406,plain,(
    ~ spl12_53 ),
    inference(avatar_split_clause,[],[f122,f404])).

fof(f122,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    & k1_tsep_1(sK0,sK2,sK3) = sK0
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & v1_borsuk_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & v1_borsuk_1(sK2,sK0)
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
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & k1_tsep_1(X0,X2,X3) = X0
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
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
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(sK0,X2,X3) = sK0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & v1_borsuk_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0)
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
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X4)
                        & k1_tsep_1(X0,X2,X3) = X0
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                        & v5_pre_topc(X5,X3,sK1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v5_pre_topc(X4,X2,sK1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_borsuk_1(X2,X0)
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
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                      & k1_tsep_1(X0,X2,X3) = X0
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK2,X3,X4,X5),X0,X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),X3,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),sK2,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X4)
                    & k1_tsep_1(X0,sK2,X3) = X0
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK2,X1)
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & v1_borsuk_1(sK2,X0)
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
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & v1_borsuk_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK3,X4,X5),X0,X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5)) )
                & r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),sK3,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),X2,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X4)
                & k1_tsep_1(X0,X2,sK3) = X0
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK3,X1)
                & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & v1_borsuk_1(sK3,X0)
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
              & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
              & k1_tsep_1(X0,X2,X3) = X0
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
            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),X5)
            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),sK4)
            & k1_tsep_1(X0,X2,X3) = X0
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
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
          & k1_tsep_1(X0,X2,X3) = X0
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK5),X0,X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK5),u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5)) )
        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),sK5)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),X4)
        & k1_tsep_1(X0,X2,X3) = X0
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
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
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
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                                & k1_tsep_1(X0,X2,X3) = X0 )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
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
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                              & k1_tsep_1(X0,X2,X3) = X0 )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t152_tmap_1.p',t152_tmap_1)).

fof(f399,plain,(
    spl12_50 ),
    inference(avatar_split_clause,[],[f123,f397])).

fof(f123,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f392,plain,(
    spl12_48 ),
    inference(avatar_split_clause,[],[f124,f390])).

fof(f124,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f385,plain,(
    ~ spl12_47 ),
    inference(avatar_split_clause,[],[f125,f383])).

fof(f125,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f378,plain,(
    spl12_44 ),
    inference(avatar_split_clause,[],[f126,f376])).

fof(f126,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f371,plain,(
    spl12_42 ),
    inference(avatar_split_clause,[],[f127,f369])).

fof(f127,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f364,plain,(
    ~ spl12_41 ),
    inference(avatar_split_clause,[],[f128,f362])).

fof(f128,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f106])).

fof(f357,plain,(
    spl12_38 ),
    inference(avatar_split_clause,[],[f129,f355])).

fof(f129,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f350,plain,(
    spl12_36 ),
    inference(avatar_split_clause,[],[f130,f348])).

fof(f130,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f343,plain,(
    ~ spl12_35 ),
    inference(avatar_split_clause,[],[f131,f341])).

fof(f131,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f106])).

fof(f336,plain,(
    spl12_32 ),
    inference(avatar_split_clause,[],[f132,f334])).

fof(f132,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f329,plain,(
    spl12_30 ),
    inference(avatar_split_clause,[],[f133,f327])).

fof(f133,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f106])).

fof(f322,plain,(
    spl12_28 ),
    inference(avatar_split_clause,[],[f134,f320])).

fof(f134,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f106])).

fof(f315,plain,(
    spl12_26 ),
    inference(avatar_split_clause,[],[f135,f313])).

fof(f135,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f106])).

fof(f308,plain,(
    spl12_24 ),
    inference(avatar_split_clause,[],[f136,f306])).

fof(f306,plain,
    ( spl12_24
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f136,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f301,plain,(
    spl12_22 ),
    inference(avatar_split_clause,[],[f137,f299])).

fof(f137,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f106])).

fof(f294,plain,(
    spl12_20 ),
    inference(avatar_split_clause,[],[f138,f292])).

fof(f138,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f106])).

fof(f287,plain,(
    spl12_18 ),
    inference(avatar_split_clause,[],[f139,f285])).

fof(f139,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f106])).

fof(f280,plain,(
    spl12_16 ),
    inference(avatar_split_clause,[],[f140,f278])).

fof(f140,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f106])).

fof(f273,plain,(
    spl12_14 ),
    inference(avatar_split_clause,[],[f141,f271])).

fof(f141,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f106])).

fof(f266,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f142,f264])).

fof(f142,plain,(
    k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f106])).

fof(f259,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f143,f257])).

fof(f143,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f106])).

fof(f252,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f144,f250])).

fof(f144,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f106])).

fof(f245,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | ~ spl12_5
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f145,f243,f237,f231,f225])).

fof(f145,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f106])).
%------------------------------------------------------------------------------

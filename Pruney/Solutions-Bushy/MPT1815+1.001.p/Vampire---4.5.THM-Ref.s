%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1815+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  275 (1562 expanded)
%              Number of leaves         :   25 ( 676 expanded)
%              Depth                    :   32
%              Number of atoms          : 1826 (50528 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f544,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f143,f144,f145,f146,f147,f148,f149,f150,f151,f152,f153,f154,f155,f156,f157,f158,f159,f160,f161,f162,f163,f164,f165,f166,f167,f168,f169,f170,f171,f172,f173,f174,f319,f332,f341,f345,f347,f349,f370,f386,f407,f482,f484,f489,f491,f523,f525,f543])).

fof(f543,plain,
    ( spl7_12
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | spl7_12
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f470,f141])).

fof(f141,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_12
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f470,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP1(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP1(X1,X3,X4,X0,X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP1(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP1(X1,X3,X4,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( sP1(X1,X3,X4,X0,X2)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f355,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl7_23
  <=> sP1(sK3,sK6,sK4,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f525,plain,
    ( spl7_6
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | spl7_6
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f464,f117])).

fof(f117,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_6
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f464,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f523,plain,
    ( spl7_10
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl7_10
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f468,f133])).

fof(f133,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_10
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f468,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f491,plain,
    ( spl7_5
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | spl7_5
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f377,f113])).

fof(f113,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_5
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f377,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f489,plain,
    ( spl7_9
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl7_9
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f381,f129])).

fof(f129,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f381,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f484,plain,
    ( spl7_8
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f483])).

fof(f483,plain,
    ( $false
    | spl7_8
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f466,f125])).

fof(f125,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_8
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f466,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f482,plain,
    ( spl7_7
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | spl7_7
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f465,f121])).

fof(f121,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_7
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f465,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f407,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_22 ),
    inference(subsumption_resolution,[],[f405,f96])).

fof(f96,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_1
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f405,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_22 ),
    inference(subsumption_resolution,[],[f404,f100])).

fof(f100,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_2
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f404,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_22 ),
    inference(subsumption_resolution,[],[f403,f104])).

fof(f104,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_3
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f403,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | ~ spl7_4
    | spl7_22 ),
    inference(subsumption_resolution,[],[f398,f330])).

fof(f330,plain,
    ( ~ sP0(sK3,sK6,sK5,sK2,sK4)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl7_22
  <=> sP0(sK3,sK6,sK5,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f398,plain,
    ( sP0(sK3,sK6,sK5,sK2,sK4)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | ~ spl7_4 ),
    inference(resolution,[],[f108,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1))) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1))) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( ( sP0(X1,X3,X2,X0,X4)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
        | ~ sP0(X1,X3,X2,X0,X4) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( ( sP0(X1,X3,X2,X0,X4)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
        | ~ sP0(X1,X3,X2,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X3,X2,X0,X4] :
      ( sP0(X1,X3,X2,X0,X4)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f108,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_4
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f386,plain,
    ( spl7_11
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | spl7_11
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f383,f137])).

fof(f137,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_11
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f383,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ spl7_23 ),
    inference(resolution,[],[f355,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f370,plain,
    ( ~ spl7_21
    | ~ spl7_22
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl7_21
    | ~ spl7_22
    | spl7_23 ),
    inference(subsumption_resolution,[],[f368,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ) )
    & m1_pre_topc(sK6,sK2)
    & v1_tsep_1(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f20,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                        & m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4))) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4))) ) )
                      & m1_pre_topc(X4,sK2)
                      & v1_tsep_1(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                      | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4))) )
                    & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                      | ( m1_subset_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,k1_tsep_1(sK2,X3,X4))) ) )
                    & m1_pre_topc(X4,sK2)
                    & v1_tsep_1(X4,sK2)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK2)
                & v1_tsep_1(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4))) )
                  & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                      & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                    | ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4))) ) )
                  & m1_pre_topc(X4,sK2)
                  & v1_tsep_1(X4,sK2)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK2)
              & v1_tsep_1(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                  | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                  | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4))) )
                & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                  | ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,k1_tsep_1(sK2,X3,X4))) ) )
                & m1_pre_topc(X4,sK2)
                & v1_tsep_1(X4,sK2)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK2)
            & v1_tsep_1(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
                | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4))) )
              & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                  & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
                | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4))) ) )
              & m1_pre_topc(X4,sK2)
              & v1_tsep_1(X4,sK2)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK2)
          & v1_tsep_1(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
              | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4))) )
            & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
              | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),k1_tsep_1(sK2,X3,X4),sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4)),u1_struct_0(k1_tsep_1(sK2,X3,X4)),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X3,X4))) ) )
            & m1_pre_topc(X4,sK2)
            & v1_tsep_1(X4,sK2)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK2)
        & v1_tsep_1(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
            | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_tsep_1(sK2,sK5,X4),sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4))) )
          & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
            | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_tsep_1(sK2,sK5,X4),sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4))) ) )
          & m1_pre_topc(X4,sK2)
          & v1_tsep_1(X4,sK2)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK5,sK2)
      & v1_tsep_1(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
          | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
          | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_tsep_1(sK2,sK5,X4),sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4))) )
        & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
          | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),k1_tsep_1(sK2,sK5,X4),sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4)),u1_struct_0(k1_tsep_1(sK2,sK5,X4)),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,X4))) ) )
        & m1_pre_topc(X4,sK2)
        & v1_tsep_1(X4,sK2)
        & ~ v2_struct_0(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) )
      & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
          & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
        | ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ) )
      & m1_pre_topc(sK6,sK2)
      & v1_tsep_1(sK6,sK2)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
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
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_tsep_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_tmap_1)).

fof(f368,plain,
    ( v2_struct_0(sK5)
    | ~ spl7_21
    | ~ spl7_22
    | spl7_23 ),
    inference(subsumption_resolution,[],[f367,f40])).

fof(f40,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f367,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_21
    | ~ spl7_22
    | spl7_23 ),
    inference(subsumption_resolution,[],[f366,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f366,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_21
    | ~ spl7_22
    | spl7_23 ),
    inference(subsumption_resolution,[],[f365,f43])).

fof(f43,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f365,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_21
    | ~ spl7_22
    | spl7_23 ),
    inference(subsumption_resolution,[],[f364,f326])).

fof(f326,plain,
    ( r4_tsep_1(sK2,sK5,sK6)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl7_21
  <=> r4_tsep_1(sK2,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f364,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_22
    | spl7_23 ),
    inference(subsumption_resolution,[],[f363,f354])).

fof(f354,plain,
    ( ~ sP1(sK3,sK6,sK4,sK2,sK5)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f353])).

fof(f363,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_22 ),
    inference(resolution,[],[f331,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f189,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f188,f30])).

fof(f30,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f187,f31])).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f186,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f185,f33])).

fof(f33,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f184,f34])).

fof(f34,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f183,f35])).

fof(f35,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f179,f36])).

fof(f36,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X0,X1,sK2,sK4)
      | sP1(sK3,X0,sK4,sK2,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f91,f37])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ sP0(X1,X3,X2,X0,X4)
      | sP1(X1,X3,X4,X0,X2)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( sP0(X1,X3,X2,X0,X4)
                          | ~ sP1(X1,X3,X4,X0,X2) )
                        & ( sP1(X1,X3,X4,X0,X2)
                          | ~ sP0(X1,X3,X2,X0,X4) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( sP0(X1,X3,X2,X0,X4)
                      <=> sP1(X1,X3,X4,X0,X2) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f331,plain,
    ( sP0(sK3,sK6,sK5,sK2,sK4)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f329])).

fof(f349,plain,
    ( spl7_4
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f331,f178])).

fof(f178,plain,
    ( ~ sP0(sK3,sK6,sK5,sK2,sK4)
    | spl7_4 ),
    inference(resolution,[],[f89,f109])).

fof(f109,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f347,plain,
    ( spl7_2
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f331,f177])).

fof(f177,plain,
    ( ~ sP0(sK3,sK6,sK5,sK2,sK4)
    | spl7_2 ),
    inference(resolution,[],[f87,f101])).

fof(f101,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f345,plain,
    ( spl7_3
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl7_3
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f331,f176])).

fof(f176,plain,
    ( ~ sP0(sK3,sK6,sK5,sK2,sK4)
    | spl7_3 ),
    inference(resolution,[],[f88,f105])).

fof(f105,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f341,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | spl7_21 ),
    inference(subsumption_resolution,[],[f339,f29])).

fof(f339,plain,
    ( v2_struct_0(sK2)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f338,f30])).

fof(f338,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f337,f31])).

fof(f337,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f336,f39])).

fof(f39,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f336,plain,
    ( ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f335,f40])).

fof(f335,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f334,f42])).

fof(f42,plain,(
    v1_tsep_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f334,plain,
    ( ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f333,f43])).

fof(f333,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_21 ),
    inference(resolution,[],[f327,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).

fof(f327,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f325])).

fof(f332,plain,
    ( ~ spl7_21
    | spl7_22
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f323,f139,f135,f131,f127,f123,f119,f115,f111,f329,f325])).

fof(f323,plain,
    ( sP0(sK3,sK6,sK5,sK2,sK4)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f322,f38])).

fof(f322,plain,
    ( sP0(sK3,sK6,sK5,sK2,sK4)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f321,f40])).

fof(f321,plain,
    ( sP0(sK3,sK6,sK5,sK2,sK4)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f320,f41])).

fof(f320,plain,
    ( sP0(sK3,sK6,sK5,sK2,sK4)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f297,f43])).

fof(f297,plain,
    ( sP0(sK3,sK6,sK5,sK2,sK4)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f264,f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f239,f29])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f238,f30])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f237,f31])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f236,f32])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f235,f33])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f234,f34])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f233,f35])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f229,f36])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X0,sK4,sK2,X1)
      | sP0(sK3,X0,X1,sK2,sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X1,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f92,f37])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ sP1(X1,X3,X4,X0,X2)
      | sP0(X1,X3,X2,X0,X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
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
    inference(cnf_transformation,[],[f28])).

fof(f264,plain,
    ( sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f263,f128])).

fof(f128,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f263,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f262,f132])).

fof(f132,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f262,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f257,f136])).

fof(f136,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f257,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP1(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(resolution,[],[f249,f140])).

fof(f140,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP1(sK3,X0,sK4,sK2,sK5) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f248,f112])).

fof(f112,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP1(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f247,f116])).

fof(f116,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP1(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f244,f120])).

fof(f120,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP1(sK3,X0,sK4,sK2,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f85,f124])).

fof(f124,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | sP1(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f319,plain,
    ( spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f317,f29])).

fof(f317,plain,
    ( v2_struct_0(sK2)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f316,f30])).

fof(f316,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f315,f31])).

fof(f315,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f314,f39])).

fof(f314,plain,
    ( ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f313,f40])).

fof(f313,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f312,f42])).

fof(f312,plain,
    ( ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f311,f43])).

fof(f311,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | ~ v1_tsep_1(sK6,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ v1_tsep_1(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f310,f93])).

fof(f310,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f309,f38])).

fof(f309,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK5)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f308,f40])).

fof(f308,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f307,f41])).

fof(f307,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f306,f43])).

fof(f306,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f297,f175])).

fof(f175,plain,
    ( ~ sP0(sK3,sK6,sK5,sK2,sK4)
    | spl7_1 ),
    inference(resolution,[],[f86,f97])).

fof(f97,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f174,plain,
    ( spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f44,f111,f95])).

fof(f44,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f173,plain,
    ( spl7_2
    | spl7_5 ),
    inference(avatar_split_clause,[],[f45,f111,f99])).

fof(f45,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f172,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f46,f111,f103])).

fof(f46,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f171,plain,
    ( spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f47,f111,f107])).

fof(f47,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f170,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f48,f115,f95])).

fof(f48,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f169,plain,
    ( spl7_2
    | spl7_6 ),
    inference(avatar_split_clause,[],[f49,f115,f99])).

fof(f49,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f168,plain,
    ( spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f50,f115,f103])).

fof(f50,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f167,plain,
    ( spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f51,f115,f107])).

fof(f51,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f166,plain,
    ( spl7_1
    | spl7_7 ),
    inference(avatar_split_clause,[],[f52,f119,f95])).

fof(f52,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f165,plain,
    ( spl7_2
    | spl7_7 ),
    inference(avatar_split_clause,[],[f53,f119,f99])).

fof(f53,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f164,plain,
    ( spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f54,f119,f103])).

fof(f54,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f163,plain,
    ( spl7_4
    | spl7_7 ),
    inference(avatar_split_clause,[],[f55,f119,f107])).

fof(f55,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f162,plain,
    ( spl7_1
    | spl7_8 ),
    inference(avatar_split_clause,[],[f56,f123,f95])).

fof(f56,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f161,plain,
    ( spl7_2
    | spl7_8 ),
    inference(avatar_split_clause,[],[f57,f123,f99])).

fof(f57,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f160,plain,
    ( spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f58,f123,f103])).

fof(f58,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f159,plain,
    ( spl7_4
    | spl7_8 ),
    inference(avatar_split_clause,[],[f59,f123,f107])).

fof(f59,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f158,plain,
    ( spl7_1
    | spl7_9 ),
    inference(avatar_split_clause,[],[f60,f127,f95])).

fof(f60,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f157,plain,
    ( spl7_2
    | spl7_9 ),
    inference(avatar_split_clause,[],[f61,f127,f99])).

fof(f61,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f156,plain,
    ( spl7_3
    | spl7_9 ),
    inference(avatar_split_clause,[],[f62,f127,f103])).

fof(f62,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f155,plain,
    ( spl7_4
    | spl7_9 ),
    inference(avatar_split_clause,[],[f63,f127,f107])).

fof(f63,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f154,plain,
    ( spl7_1
    | spl7_10 ),
    inference(avatar_split_clause,[],[f64,f131,f95])).

fof(f64,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f153,plain,
    ( spl7_2
    | spl7_10 ),
    inference(avatar_split_clause,[],[f65,f131,f99])).

fof(f65,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f152,plain,
    ( spl7_3
    | spl7_10 ),
    inference(avatar_split_clause,[],[f66,f131,f103])).

fof(f66,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,
    ( spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f67,f131,f107])).

fof(f67,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f150,plain,
    ( spl7_1
    | spl7_11 ),
    inference(avatar_split_clause,[],[f68,f135,f95])).

fof(f68,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f149,plain,
    ( spl7_2
    | spl7_11 ),
    inference(avatar_split_clause,[],[f69,f135,f99])).

fof(f69,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f148,plain,
    ( spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f70,f135,f103])).

fof(f70,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f147,plain,
    ( spl7_4
    | spl7_11 ),
    inference(avatar_split_clause,[],[f71,f135,f107])).

fof(f71,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,
    ( spl7_1
    | spl7_12 ),
    inference(avatar_split_clause,[],[f72,f139,f95])).

fof(f72,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

fof(f145,plain,
    ( spl7_2
    | spl7_12 ),
    inference(avatar_split_clause,[],[f73,f139,f99])).

fof(f73,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,
    ( spl7_3
    | spl7_12 ),
    inference(avatar_split_clause,[],[f74,f139,f103])).

fof(f74,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,
    ( spl7_4
    | spl7_12 ),
    inference(avatar_split_clause,[],[f75,f139,f107])).

fof(f75,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f142,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f76,f139,f135,f131,f127,f123,f119,f115,f111,f107,f103,f99,f95])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(k1_tsep_1(sK2,sK5,sK6)),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6))) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------

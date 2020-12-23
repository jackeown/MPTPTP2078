%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 488 expanded)
%              Number of leaves         :   37 ( 188 expanded)
%              Depth                    :   25
%              Number of atoms          : 1642 (3779 expanded)
%              Number of equality atoms :   48 ( 136 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f102,f106,f116,f120,f124,f128,f199,f203,f211,f215,f224,f229,f258,f344,f368,f462,f482,f483,f490,f504,f505])).

fof(f505,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_tmap_1(sK3,sK0,sK4,sK2)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f504,plain,
    ( spl7_41
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f499,f488,f227,f222,f122,f118,f104,f100,f96,f92,f88,f84,f72,f502])).

fof(f502,plain,
    ( spl7_41
  <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f72,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f84,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f88,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f92,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f96,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f100,plain,
    ( spl7_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f104,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f118,plain,
    ( spl7_12
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f122,plain,
    ( spl7_13
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f222,plain,
    ( spl7_21
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f227,plain,
    ( spl7_22
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f488,plain,
    ( spl7_40
  <=> k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f499,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(forward_demodulation,[],[f497,f489])).

fof(f489,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f488])).

fof(f497,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(resolution,[],[f406,f119])).

fof(f119,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f406,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f405,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f405,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f404,f223])).

fof(f223,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f222])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f403,f73])).

fof(f73,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f402,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f401,f101])).

fof(f101,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(resolution,[],[f174,f228])).

fof(f228,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f174,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f173,f170])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f169,f89])).

fof(f89,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f152,f93])).

fof(f93,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | m1_pre_topc(X0,sK1) )
    | ~ spl7_13 ),
    inference(resolution,[],[f123,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f123,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f173,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f172,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f172,plain,
    ( ! [X2,X3,X1] :
        ( v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f171,f93])).

fof(f171,plain,
    ( ! [X2,X3,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f153,f89])).

fof(f153,plain,
    ( ! [X2,X3,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
        | ~ m1_pre_topc(X2,sK3)
        | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2)) )
    | ~ spl7_13 ),
    inference(resolution,[],[f123,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f490,plain,
    ( spl7_40
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f381,f227,f222,f213,f197,f118,f104,f100,f96,f76,f72,f488])).

fof(f76,plain,
    ( spl7_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f197,plain,
    ( spl7_15
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f213,plain,
    ( spl7_19
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f381,plain,
    ( k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(resolution,[],[f239,f119])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f238,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f238,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f237,f223])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_1
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f236,f73])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f235,f105])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl7_7
    | ~ spl7_8
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f234,f101])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | spl7_7
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f233,f97])).

fof(f233,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f232,f198])).

fof(f198,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f197])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f230,f214])).

fof(f214,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f213])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl7_22 ),
    inference(resolution,[],[f228,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f483,plain,
    ( spl7_24
    | spl7_25 ),
    inference(avatar_split_clause,[],[f281,f256,f253])).

fof(f253,plain,
    ( spl7_24
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f256,plain,
    ( spl7_25
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f281,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f70,f257])).

fof(f257,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f256])).

fof(f70,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f32,f35])).

fof(f35,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f32,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f482,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_21
    | ~ spl7_22
    | spl7_24
    | ~ spl7_25
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_21
    | ~ spl7_22
    | spl7_24
    | ~ spl7_25
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f480,f254])).

fof(f254,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f480,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_25
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f479,f85])).

fof(f479,plain,
    ( v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_25
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f478,f210])).

fof(f210,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl7_18
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f478,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_25
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f477,f202])).

% (8968)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f202,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f477,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_25
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f476,f119])).

fof(f476,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_25
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f475,f367])).

fof(f367,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl7_34
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f475,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f474,f228])).

fof(f474,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f473,f223])).

fof(f473,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f472,f73])).

fof(f472,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f471,f123])).

fof(f471,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f470,f77])).

fof(f470,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f469,f127])).

fof(f127,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_14
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f469,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f468,f81])).

fof(f81,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f468,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f467,f105])).

fof(f467,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f466,f101])).

fof(f466,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f465,f97])).

fof(f465,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f464,f93])).

fof(f464,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f463,f89])).

fof(f463,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_25 ),
    inference(resolution,[],[f279,f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | X5 != X6
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f279,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f256])).

fof(f462,plain,
    ( spl7_39
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f396,f253,f227,f222,f213,f209,f201,f197,f118,f104,f100,f96,f80,f76,f72,f460])).

fof(f460,plain,
    ( spl7_39
  <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f396,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f395,f297])).

fof(f297,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f395,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f394,f81])).

fof(f394,plain,
    ( v2_struct_0(sK2)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f393,f202])).

fof(f393,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f388,f119])).

fof(f388,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(resolution,[],[f247,f210])).

fof(f247,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | ~ spl7_1
    | spl7_2
    | spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f246,f97])).

fof(f246,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f245,f223])).

fof(f245,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | ~ spl7_1
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f244,f73])).

fof(f244,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f243,f198])).

fof(f243,plain,
    ( ! [X2,X1] :
        ( ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f242,f214])).

fof(f242,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | spl7_2
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f241,f77])).

fof(f241,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f240,f105])).

fof(f240,plain,
    ( ! [X2,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f231,f101])).

fof(f231,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) )
    | ~ spl7_22 ),
    inference(resolution,[],[f228,f67])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f56])).

% (8953)Refutation not found, incomplete strategy% (8953)------------------------------
% (8953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8953)Termination reason: Refutation not found, incomplete strategy

% (8953)Memory used [KB]: 10618
% (8953)Time elapsed: 0.093 s
% (8953)------------------------------
% (8953)------------------------------
fof(f56,plain,(
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
    inference(cnf_transformation,[],[f20])).

% (8956)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f368,plain,
    ( spl7_34
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f364,f342,f126,f122,f114,f92,f88,f84,f76,f366])).

fof(f114,plain,
    ( spl7_11
  <=> v1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f342,plain,
    ( spl7_30
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f364,plain,
    ( v1_tsep_1(sK2,sK3)
    | spl7_2
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f363,f77])).

fof(f363,plain,
    ( v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f361,f123])).

fof(f361,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | v1_tsep_1(sK2,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_30 ),
    inference(resolution,[],[f134,f343])).

fof(f343,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f342])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | v1_tsep_1(sK2,X0) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f133,f127])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f132,f85])).

fof(f132,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f131,f93])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f129,f89])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | v1_tsep_1(sK2,X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f115,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f115,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f344,plain,
    ( spl7_30
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f162,f122,f118,f92,f342])).

fof(f162,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f139,f156])).

fof(f156,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f150,f93])).

fof(f150,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f123,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f139,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_12 ),
    inference(resolution,[],[f119,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f258,plain,
    ( ~ spl7_24
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f69,f256,f253])).

fof(f69,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(forward_demodulation,[],[f33,f35])).

fof(f33,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f229,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f39,f227])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f224,plain,(
    spl7_21 ),
    inference(avatar_split_clause,[],[f38,f222])).

fof(f38,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f215,plain,
    ( spl7_19
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f164,f122,f92,f88,f213])).

fof(f164,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f163,f89])).

fof(f163,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f151,f93])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f123,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f211,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f68,f209])).

fof(f68,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f34,f35])).

fof(f34,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f203,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f36,f201])).

fof(f36,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f199,plain,
    ( spl7_15
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f156,f122,f92,f197])).

fof(f128,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f46,f126])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f124,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f44,f122])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f120,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f42,f118])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f40,f114])).

fof(f40,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f106,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f52,f104])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f102,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f51,f100])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f49,f92])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f43,f76])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (8962)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (8952)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (8969)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (8952)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (8954)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (8955)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (8972)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (8971)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (8958)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (8972)Refutation not found, incomplete strategy% (8972)------------------------------
% 0.21/0.50  % (8972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8972)Memory used [KB]: 10618
% 0.21/0.50  % (8972)Time elapsed: 0.032 s
% 0.21/0.50  % (8972)------------------------------
% 0.21/0.50  % (8972)------------------------------
% 0.21/0.50  % (8957)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (8953)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f506,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f102,f106,f116,f120,f124,f128,f199,f203,f211,f215,f224,f229,f258,f344,f368,f462,f482,f483,f490,f504,f505])).
% 0.21/0.51  fof(f505,plain,(
% 0.21/0.51    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) != k2_tmap_1(sK3,sK0,sK4,sK2) | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f504,plain,(
% 0.21/0.51    spl7_41 | ~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_21 | ~spl7_22 | ~spl7_40),
% 0.21/0.51    inference(avatar_split_clause,[],[f499,f488,f227,f222,f122,f118,f104,f100,f96,f92,f88,f84,f72,f502])).
% 0.21/0.51  fof(f502,plain,(
% 0.21/0.51    spl7_41 <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl7_1 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl7_4 <=> v2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl7_5 <=> v2_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl7_6 <=> l1_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl7_7 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl7_8 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl7_9 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl7_12 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl7_13 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    spl7_21 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    spl7_22 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    spl7_40 <=> k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.21/0.51  fof(f499,plain,(
% 0.21/0.51    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_21 | ~spl7_22 | ~spl7_40)),
% 0.21/0.51    inference(forward_demodulation,[],[f497,f489])).
% 0.21/0.51  fof(f489,plain,(
% 0.21/0.51    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | ~spl7_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f488])).
% 0.21/0.51  fof(f497,plain,(
% 0.21/0.51    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(resolution,[],[f406,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK3) | ~spl7_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f118])).
% 0.21/0.51  fof(f406,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f405,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f404,f223])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f222])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f403,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    v1_funct_1(sK4) | ~spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f402,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl7_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_8 | ~spl7_13 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f401,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    v2_pre_topc(sK0) | ~spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | ~spl7_22)),
% 0.21/0.51    inference(resolution,[],[f174,f228])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~spl7_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f227])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f173,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    v2_pre_topc(sK1) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | (~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | ~spl7_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK1)) ) | ~spl7_13),
% 0.21/0.51    inference(resolution,[],[f123,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK1) | ~spl7_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f172,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~v2_struct_0(sK1) | spl7_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f171,f93])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | (~spl7_5 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f89])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,sK3) | k3_tmap_1(sK1,X1,sK3,X2,X3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X3,u1_struct_0(X2))) ) | ~spl7_13),
% 0.21/0.51    inference(resolution,[],[f123,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.51  fof(f490,plain,(
% 0.21/0.51    spl7_40 | ~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f381,f227,f222,f213,f197,f118,f104,f100,f96,f76,f72,f488])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl7_2 <=> v2_struct_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    spl7_15 <=> l1_pre_topc(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl7_19 <=> v2_pre_topc(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    k2_tmap_1(sK3,sK0,sK4,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(resolution,[],[f239,f119])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f238,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~v2_struct_0(sK3) | spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_1 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f237,f223])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_1 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f236,f73])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f235,f105])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl7_7 | ~spl7_8 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f234,f101])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (spl7_7 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f233,f97])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f232,f198])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    l1_pre_topc(sK3) | ~spl7_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f197])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | (~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f230,f214])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    v2_pre_topc(sK3) | ~spl7_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f213])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK3) | ~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK0,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | ~spl7_22),
% 0.21/0.51    inference(resolution,[],[f228,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.51  fof(f483,plain,(
% 0.21/0.51    spl7_24 | spl7_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f281,f256,f253])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    spl7_24 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    spl7_25 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_25),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f257])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | spl7_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f256])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f32,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    sK5 = sK6),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f482,plain,(
% 0.21/0.51    ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_21 | ~spl7_22 | spl7_24 | ~spl7_25 | ~spl7_34),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f481])).
% 0.21/0.51  fof(f481,plain,(
% 0.21/0.51    $false | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_21 | ~spl7_22 | spl7_24 | ~spl7_25 | ~spl7_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f480,f254])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f253])).
% 0.21/0.51  fof(f480,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_21 | ~spl7_22 | ~spl7_25 | ~spl7_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f479,f85])).
% 0.21/0.51  fof(f479,plain,(
% 0.21/0.51    v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_18 | ~spl7_21 | ~spl7_22 | ~spl7_25 | ~spl7_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f478,f210])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl7_18 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.51  fof(f478,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_16 | ~spl7_21 | ~spl7_22 | ~spl7_25 | ~spl7_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f477,f202])).
% 0.21/0.51  % (8968)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f201])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl7_16 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.51  fof(f477,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_21 | ~spl7_22 | ~spl7_25 | ~spl7_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f476,f119])).
% 0.21/0.51  fof(f476,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_21 | ~spl7_22 | ~spl7_25 | ~spl7_34)),
% 0.21/0.51    inference(subsumption_resolution,[],[f475,f367])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    v1_tsep_1(sK2,sK3) | ~spl7_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f366])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    spl7_34 <=> v1_tsep_1(sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.51  fof(f475,plain,(
% 0.21/0.51    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_21 | ~spl7_22 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f474,f228])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_21 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f473,f223])).
% 0.21/0.51  fof(f473,plain,(
% 0.21/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f472,f73])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_13 | ~spl7_14 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f471,f123])).
% 0.21/0.51  fof(f471,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f470,f77])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f469,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK1) | ~spl7_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl7_14 <=> m1_pre_topc(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.51  fof(f469,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (spl7_3 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f468,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~v2_struct_0(sK2) | spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl7_3 <=> v2_struct_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f468,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f467,f105])).
% 0.21/0.51  fof(f467,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f466,f101])).
% 0.21/0.51  fof(f466,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f465,f97])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f464,f93])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | (~spl7_5 | ~spl7_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f463,f89])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | v2_struct_0(sK1) | r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_25),
% 0.21/0.51    inference(resolution,[],[f279,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.21/0.51    inference(equality_resolution,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_tsep_1(X2,X3) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | X5 != X6 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~spl7_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f256])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    spl7_39 | ~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f396,f253,f227,f222,f213,f209,f201,f197,f118,f104,f100,f96,f80,f76,f72,f460])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    spl7_39 <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22 | ~spl7_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f395,f297])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f253])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_1 | spl7_2 | spl7_3 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f394,f81])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f393,f202])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK2) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f388,f119])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK2) | ~r1_tmap_1(sK3,sK0,sK4,sK5) | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK5) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_18 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(resolution,[],[f247,f210])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | v2_struct_0(X1) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (~spl7_1 | spl7_2 | spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f246,f97])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X2,X1] : (v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_21 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f245,f223])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (~spl7_1 | spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f244,f73])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f243,f198])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_19 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f242,f214])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (spl7_2 | ~spl7_8 | ~spl7_9 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f241,f77])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ( ! [X2,X1] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (~spl7_8 | ~spl7_9 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f240,f105])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | (~spl7_8 | ~spl7_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f231,f101])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)) ) | ~spl7_22),
% 0.21/0.51    inference(resolution,[],[f228,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.51    inference(equality_resolution,[],[f56])).
% 0.21/0.51  % (8953)Refutation not found, incomplete strategy% (8953)------------------------------
% 0.21/0.51  % (8953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8953)Memory used [KB]: 10618
% 0.21/0.51  % (8953)Time elapsed: 0.093 s
% 0.21/0.51  % (8953)------------------------------
% 0.21/0.51  % (8953)------------------------------
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  % (8956)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    spl7_34 | spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f364,f342,f126,f122,f114,f92,f88,f84,f76,f366])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl7_11 <=> v1_tsep_1(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    spl7_30 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    v1_tsep_1(sK2,sK3) | (spl7_2 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_30)),
% 0.21/0.51    inference(subsumption_resolution,[],[f363,f77])).
% 0.21/0.51  fof(f363,plain,(
% 0.21/0.51    v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_30)),
% 0.21/0.51    inference(subsumption_resolution,[],[f361,f123])).
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | v1_tsep_1(sK2,sK3) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_30)),
% 0.21/0.51    inference(resolution,[],[f134,f343])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f342])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11 | ~spl7_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f133,f127])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f132,f85])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_6 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f93])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | (~spl7_5 | ~spl7_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f89])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | v1_tsep_1(sK2,X0)) ) | ~spl7_11),
% 0.21/0.51    inference(resolution,[],[f115,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_tsep_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    v1_tsep_1(sK2,sK1) | ~spl7_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    spl7_30 | ~spl7_6 | ~spl7_12 | ~spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f162,f122,f118,f92,f342])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | (~spl7_6 | ~spl7_12 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    l1_pre_topc(sK3) | (~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f93])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | l1_pre_topc(sK3) | ~spl7_13),
% 0.21/0.51    inference(resolution,[],[f123,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~l1_pre_topc(sK3) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_12),
% 0.21/0.51    inference(resolution,[],[f119,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ~spl7_24 | ~spl7_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f69,f256,f253])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(forward_demodulation,[],[f33,f35])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    spl7_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f227])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    spl7_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f222])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    spl7_19 | ~spl7_5 | ~spl7_6 | ~spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f164,f122,f92,f88,f213])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    v2_pre_topc(sK3) | (~spl7_5 | ~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f89])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~v2_pre_topc(sK1) | v2_pre_topc(sK3) | (~spl7_6 | ~spl7_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f151,f93])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_pre_topc(sK3) | ~spl7_13),
% 0.21/0.51    inference(resolution,[],[f123,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    spl7_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f209])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.51    inference(forward_demodulation,[],[f34,f35])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl7_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f201])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    spl7_15 | ~spl7_6 | ~spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f156,f122,f92,f197])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl7_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f126])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f122])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl7_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f118])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl7_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f114])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v1_tsep_1(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl7_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f104])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl7_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f100])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f96])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f92])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    l1_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f88])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v2_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f84])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f80])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~v2_struct_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f76])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~v2_struct_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f72])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (8952)------------------------------
% 0.21/0.51  % (8952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8952)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (8952)Memory used [KB]: 6524
% 0.21/0.51  % (8952)Time elapsed: 0.077 s
% 0.21/0.51  % (8952)------------------------------
% 0.21/0.51  % (8952)------------------------------
% 0.21/0.51  % (8951)Success in time 0.151 s
%------------------------------------------------------------------------------

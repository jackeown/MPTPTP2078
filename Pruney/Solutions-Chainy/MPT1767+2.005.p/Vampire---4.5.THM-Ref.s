%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 251 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  439 (1878 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f122,f124,f130,f140,f155,f163,f164,f171,f182,f186,f237,f240,f243])).

fof(f243,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl6_25 ),
    inference(resolution,[],[f233,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f233,plain,
    ( ~ v1_funct_2(sK5(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_25
  <=> v1_funct_2(sK5(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f240,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl6_26 ),
    inference(resolution,[],[f236,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f236,plain,
    ( ~ v1_funct_1(sK5(u1_struct_0(sK3),u1_struct_0(sK1)))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl6_26
  <=> v1_funct_1(sK5(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f237,plain,
    ( ~ spl6_25
    | ~ spl6_26
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f226,f184,f235,f232])).

fof(f184,plain,
    ( spl6_17
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f226,plain,
    ( ~ v1_funct_1(sK5(u1_struct_0(sK3),u1_struct_0(sK1)))
    | ~ v1_funct_2(sK5(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_17 ),
    inference(resolution,[],[f185,f47])).

fof(f47,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f186,plain,
    ( ~ spl6_8
    | spl6_17
    | ~ spl6_6
    | ~ spl6_7
    | spl6_5 ),
    inference(avatar_split_clause,[],[f128,f91,f97,f94,f184,f100])).

fof(f100,plain,
    ( spl6_8
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f94,plain,
    ( spl6_6
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f97,plain,
    ( spl6_7
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f91,plain,
    ( spl6_5
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) )
    | spl6_5 ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f92,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f182,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f112,f30])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f112,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f171,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl6_12 ),
    inference(resolution,[],[f115,f29])).

fof(f29,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_12
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f164,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_6 ),
    inference(avatar_split_clause,[],[f126,f94,f120,f117,f114,f111,f108,f105])).

fof(f105,plain,
    ( spl6_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f108,plain,
    ( spl6_10
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f117,plain,
    ( spl6_13
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f120,plain,
    ( spl6_14
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f126,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl6_6 ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f95,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f163,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl6_14 ),
    inference(resolution,[],[f133,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_14 ),
    inference(resolution,[],[f121,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f121,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f155,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl6_10 ),
    inference(resolution,[],[f127,f67])).

% (17793)Refutation not found, incomplete strategy% (17793)------------------------------
% (17793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(global_subsumption,[],[f42,f58])).

% (17793)Termination reason: Refutation not found, incomplete strategy

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f44,f34])).

% (17793)Memory used [KB]: 10618
fof(f34,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

% (17793)Time elapsed: 0.115 s
% (17793)------------------------------
% (17793)------------------------------
fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK3)
    | spl6_10 ),
    inference(resolution,[],[f109,f43])).

fof(f109,plain,
    ( ~ l1_struct_0(sK3)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f140,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl6_9 ),
    inference(resolution,[],[f125,f42])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_9 ),
    inference(resolution,[],[f106,f43])).

fof(f106,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f130,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f118,f28])).

fof(f28,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,
    ( ~ v1_funct_1(sK4)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f124,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_7 ),
    inference(avatar_split_clause,[],[f123,f97,f120,f117,f114,f111,f108,f105])).

fof(f123,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl6_7 ),
    inference(resolution,[],[f98,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f122,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_8 ),
    inference(avatar_split_clause,[],[f103,f100,f120,f117,f114,f111,f108,f105])).

fof(f103,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl6_8 ),
    inference(resolution,[],[f101,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f89,f100,f97,f94,f91])).

fof(f89,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(global_subsumption,[],[f28,f33,f35,f37,f38,f39,f40,f41,f42,f31,f34,f36,f29,f30,f88])).

fof(f88,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

fof(f36,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (17784)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (17787)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (17788)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.49  % (17796)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.49  % (17802)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.49  % (17789)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (17795)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (17786)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (17805)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (17798)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (17781)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (17804)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (17806)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (17793)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (17782)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (17790)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (17795)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (17803)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (17790)Refutation not found, incomplete strategy% (17790)------------------------------
% 0.22/0.52  % (17790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17797)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (17790)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17790)Memory used [KB]: 6268
% 0.22/0.52  % (17790)Time elapsed: 0.064 s
% 0.22/0.52  % (17790)------------------------------
% 0.22/0.52  % (17790)------------------------------
% 1.23/0.52  % (17792)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.23/0.52  % (17801)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.23/0.53  % (17800)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.23/0.53  % (17791)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.23/0.53  % SZS output start Proof for theBenchmark
% 1.23/0.53  fof(f244,plain,(
% 1.23/0.53    $false),
% 1.23/0.53    inference(avatar_sat_refutation,[],[f102,f122,f124,f130,f140,f155,f163,f164,f171,f182,f186,f237,f240,f243])).
% 1.23/0.53  fof(f243,plain,(
% 1.23/0.53    spl6_25),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f242])).
% 1.23/0.53  fof(f242,plain,(
% 1.23/0.53    $false | spl6_25),
% 1.23/0.53    inference(resolution,[],[f233,f49])).
% 1.23/0.53  fof(f49,plain,(
% 1.23/0.53    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f13])).
% 1.23/0.53  fof(f13,plain,(
% 1.23/0.53    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(pure_predicate_removal,[],[f12])).
% 1.23/0.53  fof(f12,plain,(
% 1.23/0.53    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(pure_predicate_removal,[],[f11])).
% 1.23/0.53  fof(f11,plain,(
% 1.23/0.53    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(pure_predicate_removal,[],[f2])).
% 1.23/0.53  fof(f2,axiom,(
% 1.23/0.53    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 1.23/0.53  fof(f233,plain,(
% 1.23/0.53    ~v1_funct_2(sK5(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(sK3),u1_struct_0(sK1)) | spl6_25),
% 1.23/0.53    inference(avatar_component_clause,[],[f232])).
% 1.23/0.53  fof(f232,plain,(
% 1.23/0.53    spl6_25 <=> v1_funct_2(sK5(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.23/0.53  fof(f240,plain,(
% 1.23/0.53    spl6_26),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f239])).
% 1.23/0.53  fof(f239,plain,(
% 1.23/0.53    $false | spl6_26),
% 1.23/0.53    inference(resolution,[],[f236,f48])).
% 1.23/0.53  fof(f48,plain,(
% 1.23/0.53    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f13])).
% 1.23/0.53  fof(f236,plain,(
% 1.23/0.53    ~v1_funct_1(sK5(u1_struct_0(sK3),u1_struct_0(sK1))) | spl6_26),
% 1.23/0.53    inference(avatar_component_clause,[],[f235])).
% 1.23/0.53  fof(f235,plain,(
% 1.23/0.53    spl6_26 <=> v1_funct_1(sK5(u1_struct_0(sK3),u1_struct_0(sK1)))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.23/0.53  fof(f237,plain,(
% 1.23/0.53    ~spl6_25 | ~spl6_26 | ~spl6_17),
% 1.23/0.53    inference(avatar_split_clause,[],[f226,f184,f235,f232])).
% 1.23/0.53  fof(f184,plain,(
% 1.23/0.53    spl6_17 <=> ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.23/0.53  fof(f226,plain,(
% 1.23/0.53    ~v1_funct_1(sK5(u1_struct_0(sK3),u1_struct_0(sK1))) | ~v1_funct_2(sK5(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_17),
% 1.23/0.53    inference(resolution,[],[f185,f47])).
% 1.23/0.53  fof(f47,plain,(
% 1.23/0.53    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f13])).
% 1.23/0.53  fof(f185,plain,(
% 1.23/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl6_17),
% 1.23/0.53    inference(avatar_component_clause,[],[f184])).
% 1.23/0.53  fof(f186,plain,(
% 1.23/0.53    ~spl6_8 | spl6_17 | ~spl6_6 | ~spl6_7 | spl6_5),
% 1.23/0.53    inference(avatar_split_clause,[],[f128,f91,f97,f94,f184,f100])).
% 1.23/0.53  fof(f100,plain,(
% 1.23/0.53    spl6_8 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.23/0.53  fof(f94,plain,(
% 1.23/0.53    spl6_6 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.23/0.53  fof(f97,plain,(
% 1.23/0.53    spl6_7 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.23/0.53  fof(f91,plain,(
% 1.23/0.53    spl6_5 <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.23/0.53  fof(f128,plain,(
% 1.23/0.53    ( ! [X0] : (~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))) ) | spl6_5),
% 1.23/0.53    inference(resolution,[],[f92,f53])).
% 1.23/0.53  fof(f53,plain,(
% 1.23/0.53    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f25])).
% 1.23/0.53  fof(f25,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.23/0.53    inference(flattening,[],[f24])).
% 1.23/0.53  fof(f24,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.23/0.53    inference(ennf_transformation,[],[f3])).
% 1.23/0.53  fof(f3,axiom,(
% 1.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.23/0.53  fof(f92,plain,(
% 1.23/0.53    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) | spl6_5),
% 1.23/0.53    inference(avatar_component_clause,[],[f91])).
% 1.23/0.53  fof(f182,plain,(
% 1.23/0.53    spl6_11),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f181])).
% 1.23/0.53  fof(f181,plain,(
% 1.23/0.53    $false | spl6_11),
% 1.23/0.53    inference(resolution,[],[f112,f30])).
% 1.23/0.53  fof(f30,plain,(
% 1.23/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f15,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f14])).
% 1.23/0.53  fof(f14,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f10])).
% 1.23/0.53  fof(f10,negated_conjecture,(
% 1.23/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 1.23/0.53    inference(negated_conjecture,[],[f9])).
% 1.23/0.53  fof(f9,conjecture,(
% 1.23/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).
% 1.23/0.53  fof(f112,plain,(
% 1.23/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl6_11),
% 1.23/0.53    inference(avatar_component_clause,[],[f111])).
% 1.23/0.53  fof(f111,plain,(
% 1.23/0.53    spl6_11 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.23/0.53  fof(f171,plain,(
% 1.23/0.53    spl6_12),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f170])).
% 1.23/0.53  fof(f170,plain,(
% 1.23/0.53    $false | spl6_12),
% 1.23/0.53    inference(resolution,[],[f115,f29])).
% 1.23/0.53  fof(f29,plain,(
% 1.23/0.53    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f115,plain,(
% 1.23/0.53    ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | spl6_12),
% 1.23/0.53    inference(avatar_component_clause,[],[f114])).
% 1.23/0.53  fof(f114,plain,(
% 1.23/0.53    spl6_12 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.23/0.53  fof(f164,plain,(
% 1.23/0.53    ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | spl6_6),
% 1.23/0.53    inference(avatar_split_clause,[],[f126,f94,f120,f117,f114,f111,f108,f105])).
% 1.23/0.53  fof(f105,plain,(
% 1.23/0.53    spl6_9 <=> l1_struct_0(sK0)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.23/0.53  fof(f108,plain,(
% 1.23/0.53    spl6_10 <=> l1_struct_0(sK3)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.23/0.53  fof(f117,plain,(
% 1.23/0.53    spl6_13 <=> v1_funct_1(sK4)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.23/0.53  fof(f120,plain,(
% 1.23/0.53    spl6_14 <=> l1_struct_0(sK1)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.23/0.53  fof(f126,plain,(
% 1.23/0.53    ~l1_struct_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl6_6),
% 1.23/0.53    inference(resolution,[],[f95,f52])).
% 1.23/0.53  fof(f52,plain,(
% 1.23/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f23])).
% 1.23/0.53  fof(f23,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f22])).
% 1.23/0.53  fof(f22,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f7])).
% 1.23/0.53  fof(f7,axiom,(
% 1.23/0.53    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.23/0.53  fof(f95,plain,(
% 1.23/0.53    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl6_6),
% 1.23/0.53    inference(avatar_component_clause,[],[f94])).
% 1.23/0.53  fof(f163,plain,(
% 1.23/0.53    spl6_14),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f162])).
% 1.23/0.53  fof(f162,plain,(
% 1.23/0.53    $false | spl6_14),
% 1.23/0.53    inference(resolution,[],[f133,f39])).
% 1.23/0.53  fof(f39,plain,(
% 1.23/0.53    l1_pre_topc(sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f133,plain,(
% 1.23/0.53    ~l1_pre_topc(sK1) | spl6_14),
% 1.23/0.53    inference(resolution,[],[f121,f43])).
% 1.23/0.53  fof(f43,plain,(
% 1.23/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f16])).
% 1.23/0.53  fof(f16,plain,(
% 1.23/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f4])).
% 1.23/0.53  fof(f4,axiom,(
% 1.23/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.23/0.53  fof(f121,plain,(
% 1.23/0.53    ~l1_struct_0(sK1) | spl6_14),
% 1.23/0.53    inference(avatar_component_clause,[],[f120])).
% 1.23/0.53  fof(f155,plain,(
% 1.23/0.53    spl6_10),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f154])).
% 1.23/0.53  fof(f154,plain,(
% 1.23/0.53    $false | spl6_10),
% 1.23/0.53    inference(resolution,[],[f127,f67])).
% 1.23/0.53  % (17793)Refutation not found, incomplete strategy% (17793)------------------------------
% 1.23/0.53  % (17793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  fof(f67,plain,(
% 1.23/0.53    l1_pre_topc(sK3)),
% 1.23/0.53    inference(global_subsumption,[],[f42,f58])).
% 1.23/0.53  % (17793)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  fof(f58,plain,(
% 1.23/0.53    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 1.23/0.53    inference(resolution,[],[f44,f34])).
% 1.23/0.53  % (17793)Memory used [KB]: 10618
% 1.23/0.53  fof(f34,plain,(
% 1.23/0.53    m1_pre_topc(sK3,sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  % (17793)Time elapsed: 0.115 s
% 1.23/0.53  % (17793)------------------------------
% 1.23/0.53  % (17793)------------------------------
% 1.23/0.53  fof(f44,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f17])).
% 1.23/0.53  fof(f17,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f5])).
% 1.23/0.53  fof(f5,axiom,(
% 1.23/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.23/0.53  fof(f42,plain,(
% 1.23/0.53    l1_pre_topc(sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f127,plain,(
% 1.23/0.53    ~l1_pre_topc(sK3) | spl6_10),
% 1.23/0.53    inference(resolution,[],[f109,f43])).
% 1.23/0.53  fof(f109,plain,(
% 1.23/0.53    ~l1_struct_0(sK3) | spl6_10),
% 1.23/0.53    inference(avatar_component_clause,[],[f108])).
% 1.23/0.53  fof(f140,plain,(
% 1.23/0.53    spl6_9),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f139])).
% 1.23/0.53  fof(f139,plain,(
% 1.23/0.53    $false | spl6_9),
% 1.23/0.53    inference(resolution,[],[f125,f42])).
% 1.23/0.53  fof(f125,plain,(
% 1.23/0.53    ~l1_pre_topc(sK0) | spl6_9),
% 1.23/0.53    inference(resolution,[],[f106,f43])).
% 1.23/0.53  fof(f106,plain,(
% 1.23/0.53    ~l1_struct_0(sK0) | spl6_9),
% 1.23/0.53    inference(avatar_component_clause,[],[f105])).
% 1.23/0.53  fof(f130,plain,(
% 1.23/0.53    spl6_13),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f129])).
% 1.23/0.53  fof(f129,plain,(
% 1.23/0.53    $false | spl6_13),
% 1.23/0.53    inference(resolution,[],[f118,f28])).
% 1.23/0.53  fof(f28,plain,(
% 1.23/0.53    v1_funct_1(sK4)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f118,plain,(
% 1.23/0.53    ~v1_funct_1(sK4) | spl6_13),
% 1.23/0.53    inference(avatar_component_clause,[],[f117])).
% 1.23/0.53  fof(f124,plain,(
% 1.23/0.53    ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | spl6_7),
% 1.23/0.53    inference(avatar_split_clause,[],[f123,f97,f120,f117,f114,f111,f108,f105])).
% 1.23/0.53  fof(f123,plain,(
% 1.23/0.53    ~l1_struct_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl6_7),
% 1.23/0.53    inference(resolution,[],[f98,f51])).
% 1.23/0.53  fof(f51,plain,(
% 1.23/0.53    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f23])).
% 1.23/0.53  fof(f98,plain,(
% 1.23/0.53    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl6_7),
% 1.23/0.53    inference(avatar_component_clause,[],[f97])).
% 1.23/0.53  fof(f122,plain,(
% 1.23/0.53    ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | spl6_8),
% 1.23/0.53    inference(avatar_split_clause,[],[f103,f100,f120,f117,f114,f111,f108,f105])).
% 1.23/0.53  fof(f103,plain,(
% 1.23/0.53    ~l1_struct_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl6_8),
% 1.23/0.53    inference(resolution,[],[f101,f50])).
% 1.23/0.53  fof(f50,plain,(
% 1.23/0.53    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f23])).
% 1.23/0.53  fof(f101,plain,(
% 1.23/0.53    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | spl6_8),
% 1.23/0.53    inference(avatar_component_clause,[],[f100])).
% 1.23/0.53  fof(f102,plain,(
% 1.23/0.53    ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8),
% 1.23/0.53    inference(avatar_split_clause,[],[f89,f100,f97,f94,f91])).
% 1.23/0.53  fof(f89,plain,(
% 1.23/0.53    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.23/0.53    inference(global_subsumption,[],[f28,f33,f35,f37,f38,f39,f40,f41,f42,f31,f34,f36,f29,f30,f88])).
% 1.23/0.53  fof(f88,plain,(
% 1.23/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0)),
% 1.23/0.53    inference(resolution,[],[f45,f32])).
% 1.23/0.53  fof(f32,plain,(
% 1.23/0.53    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f45,plain,(
% 1.23/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X3,X2) | v2_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f19])).
% 1.23/0.53  fof(f19,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f18])).
% 1.23/0.53  fof(f18,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f8])).
% 1.23/0.53  fof(f8,axiom,(
% 1.23/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).
% 1.23/0.53  fof(f36,plain,(
% 1.23/0.53    m1_pre_topc(sK2,sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f31,plain,(
% 1.23/0.53    m1_pre_topc(sK2,sK3)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f41,plain,(
% 1.23/0.53    v2_pre_topc(sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f40,plain,(
% 1.23/0.53    ~v2_struct_0(sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f38,plain,(
% 1.23/0.53    v2_pre_topc(sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f37,plain,(
% 1.23/0.53    ~v2_struct_0(sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f35,plain,(
% 1.23/0.53    ~v2_struct_0(sK2)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f33,plain,(
% 1.23/0.53    ~v2_struct_0(sK3)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  % SZS output end Proof for theBenchmark
% 1.23/0.53  % (17795)------------------------------
% 1.23/0.53  % (17795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (17795)Termination reason: Refutation
% 1.23/0.53  
% 1.23/0.53  % (17795)Memory used [KB]: 10874
% 1.23/0.53  % (17795)Time elapsed: 0.108 s
% 1.23/0.53  % (17795)------------------------------
% 1.23/0.53  % (17795)------------------------------
% 1.23/0.53  % (17799)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.23/0.53  % (17778)Success in time 0.169 s
%------------------------------------------------------------------------------

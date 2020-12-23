%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:44 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  228 (2107 expanded)
%              Number of leaves         :   39 ( 483 expanded)
%              Depth                    :   19
%              Number of atoms          : 1043 (35646 expanded)
%              Number of equality atoms :   28 (1458 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f101,f179,f203,f227,f239,f241,f253,f262,f269,f280,f287,f294,f301,f303,f602,f664,f693,f821,f841,f904,f921,f923,f925,f998,f1025,f1027,f1029,f1079,f1156,f1188])).

fof(f1188,plain,
    ( ~ spl7_2
    | ~ spl7_59 ),
    inference(avatar_contradiction_clause,[],[f1187])).

fof(f1187,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_59 ),
    inference(resolution,[],[f986,f94])).

fof(f94,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_2
  <=> sP5(sK4,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f986,plain,
    ( ! [X0] : ~ sP5(X0,sK3,sK2,sK1,sK0)
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f985])).

fof(f985,plain,
    ( spl7_59
  <=> ! [X0] : ~ sP5(X0,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f1156,plain,
    ( ~ spl7_2
    | ~ spl7_53 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_53 ),
    inference(resolution,[],[f901,f94])).

fof(f901,plain,
    ( ! [X4] : ~ sP5(sK4,X4,sK2,sK1,sK0)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl7_53
  <=> ! [X4] : ~ sP5(sK4,X4,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f1079,plain,
    ( ~ spl7_61
    | ~ spl7_62
    | ~ spl7_63
    | ~ spl7_49
    | ~ spl7_50
    | ~ spl7_51
    | ~ spl7_52
    | ~ spl7_60
    | spl7_26 ),
    inference(avatar_split_clause,[],[f1070,f600,f988,f896,f892,f888,f884,f1000,f996,f992])).

fof(f992,plain,
    ( spl7_61
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f996,plain,
    ( spl7_62
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1000,plain,
    ( spl7_63
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f884,plain,
    ( spl7_49
  <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f888,plain,
    ( spl7_50
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f892,plain,
    ( spl7_51
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f896,plain,
    ( spl7_52
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f988,plain,
    ( spl7_60
  <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f600,plain,
    ( spl7_26
  <=> sP6(sK2,sK4,sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f1070,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1069,f305])).

fof(f305,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(resolution,[],[f216,f52])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f216,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f53,f56,f57,f58,f59,f60,f61,f54,f215])).

fof(f215,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f204,f131])).

fof(f131,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) ),
    inference(global_subsumption,[],[f53,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f87,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f204,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f54,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f1069,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1068,f304])).

fof(f304,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    inference(resolution,[],[f216,f48])).

fof(f48,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f1068,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1067,f304])).

fof(f1067,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1066,f304])).

fof(f1066,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1065,f304])).

fof(f1065,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1064,f305])).

fof(f1064,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1063,f305])).

fof(f1063,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(forward_demodulation,[],[f1062,f305])).

fof(f1062,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_26 ),
    inference(resolution,[],[f820,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X4,X3,X2,X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f820,plain,
    ( ~ sP6(sK2,sK4,sK3,sK1,sK0)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f600])).

fof(f1029,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_18
    | spl7_63 ),
    inference(avatar_split_clause,[],[f1028,f1000,f201,f189,f186])).

fof(f186,plain,
    ( spl7_13
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f189,plain,
    ( spl7_14
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f201,plain,
    ( spl7_18
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1028,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f53,f54,f55,f967])).

fof(f967,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f86,f305])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f1027,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_18
    | spl7_61 ),
    inference(avatar_split_clause,[],[f1026,f992,f201,f189,f186])).

fof(f1026,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f53,f54,f55,f966])).

fof(f966,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f85,f305])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1025,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_18
    | spl7_60 ),
    inference(avatar_split_clause,[],[f1024,f988,f201,f189,f186])).

fof(f1024,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f53,f54,f55,f965])).

fof(f965,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f84,f305])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f998,plain,
    ( spl7_59
    | spl7_62 ),
    inference(avatar_split_clause,[],[f951,f996,f985])).

fof(f951,plain,(
    ! [X2] :
      ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
      | ~ sP5(X2,sK3,sK2,sK1,sK0) ) ),
    inference(superposition,[],[f36,f305])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f925,plain,
    ( ~ spl7_13
    | ~ spl7_19
    | ~ spl7_18
    | spl7_52 ),
    inference(avatar_split_clause,[],[f924,f896,f201,f260,f186])).

fof(f260,plain,
    ( spl7_19
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f924,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f53,f54,f55,f863])).

fof(f863,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f86,f304])).

fof(f923,plain,
    ( ~ spl7_13
    | ~ spl7_19
    | ~ spl7_18
    | spl7_50 ),
    inference(avatar_split_clause,[],[f922,f888,f201,f260,f186])).

fof(f922,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f53,f54,f55,f862])).

fof(f862,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f85,f304])).

fof(f921,plain,
    ( ~ spl7_13
    | ~ spl7_19
    | ~ spl7_18
    | spl7_49 ),
    inference(avatar_split_clause,[],[f920,f884,f201,f260,f186])).

fof(f920,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f53,f54,f55,f861])).

fof(f861,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f84,f304])).

fof(f904,plain,
    ( spl7_53
    | spl7_51 ),
    inference(avatar_split_clause,[],[f851,f892,f900])).

fof(f851,plain,(
    ! [X6] :
      ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
      | ~ sP5(sK4,X6,sK2,sK1,sK0) ) ),
    inference(superposition,[],[f40,f304])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f841,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | spl7_15 ),
    inference(resolution,[],[f193,f55])).

fof(f193,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl7_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f821,plain,
    ( ~ spl7_26
    | spl7_1 ),
    inference(avatar_split_clause,[],[f819,f90,f600])).

fof(f90,plain,
    ( spl7_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f819,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ sP6(sK2,sK4,sK3,sK1,sK0) ),
    inference(global_subsumption,[],[f53,f56,f57,f58,f54,f55,f556])).

fof(f556,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ sP6(sK2,sK4,sK3,sK1,sK0) ),
    inference(superposition,[],[f225,f308])).

fof(f308,plain,(
    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f306,f113])).

fof(f113,plain,(
    sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f106,f112])).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f79,f109])).

fof(f109,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f106,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f80,f55])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f306,plain,(
    k7_relat_1(sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(resolution,[],[f216,f144])).

fof(f144,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(global_subsumption,[],[f47,f51,f59,f61,f48,f52,f142])).

fof(f142,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f83,f49])).

fof(f49,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f225,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ sP6(X1,sK4,sK3,X0,sK0) ) ),
    inference(global_subsumption,[],[f47,f51,f59,f60,f61,f48,f52,f50,f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ sP6(X1,sK4,sK3,X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f76,f49])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ sP6(X4,X3,X2,X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    r4_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f693,plain,
    ( spl7_11
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl7_11
    | ~ spl7_26 ),
    inference(resolution,[],[f271,f601])).

fof(f601,plain,
    ( sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f600])).

fof(f271,plain,
    ( ! [X1] : ~ sP6(sK2,X1,sK3,sK1,sK0)
    | spl7_11 ),
    inference(resolution,[],[f175,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f175,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_11
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f664,plain,
    ( spl7_7
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | spl7_7
    | ~ spl7_26 ),
    inference(resolution,[],[f264,f601])).

fof(f264,plain,
    ( ! [X0] : ~ sP6(sK2,sK4,X0,sK1,sK0)
    | spl7_7 ),
    inference(resolution,[],[f163,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f163,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_7
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f602,plain,
    ( ~ spl7_1
    | spl7_26 ),
    inference(avatar_split_clause,[],[f598,f600,f90])).

fof(f598,plain,
    ( sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f53,f56,f57,f58,f54,f55,f597])).

fof(f597,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f553])).

fof(f553,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(superposition,[],[f251,f308])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | sP6(X1,sK4,sK3,X0,sK0)
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) ) ),
    inference(global_subsumption,[],[f47,f51,f59,f60,f61,f48,f52,f50,f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | sP6(X1,sK4,sK3,X0,sK0)
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f73,f49])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP6(X4,X3,X2,X1,X0)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f303,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl7_16 ),
    inference(resolution,[],[f196,f54])).

fof(f196,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl7_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f301,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_10 ),
    inference(avatar_split_clause,[],[f296,f171,f201,f198,f195,f192,f189,f186])).

fof(f198,plain,
    ( spl7_17
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f171,plain,
    ( spl7_10
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f296,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl7_10 ),
    inference(resolution,[],[f172,f86])).

fof(f172,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f294,plain,
    ( ~ spl7_13
    | ~ spl7_19
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_6 ),
    inference(avatar_split_clause,[],[f289,f159,f201,f198,f195,f192,f260,f186])).

fof(f159,plain,
    ( spl7_6
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f289,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | spl7_6 ),
    inference(resolution,[],[f160,f86])).

fof(f160,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f287,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_12 ),
    inference(avatar_split_clause,[],[f282,f177,f201,f198,f195,f192,f189,f186])).

fof(f177,plain,
    ( spl7_12
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f282,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl7_12 ),
    inference(resolution,[],[f178,f85])).

fof(f178,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f280,plain,
    ( ~ spl7_13
    | ~ spl7_19
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_8 ),
    inference(avatar_split_clause,[],[f275,f165,f201,f198,f195,f192,f260,f186])).

fof(f165,plain,
    ( spl7_8
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f275,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | spl7_8 ),
    inference(resolution,[],[f166,f85])).

fof(f166,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f269,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl7_19 ),
    inference(resolution,[],[f263,f104])).

fof(f104,plain,(
    l1_pre_topc(sK4) ),
    inference(global_subsumption,[],[f61,f102])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4) ),
    inference(resolution,[],[f63,f48])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f263,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_19 ),
    inference(resolution,[],[f261,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f261,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f260])).

fof(f262,plain,
    ( ~ spl7_13
    | ~ spl7_19
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_9 ),
    inference(avatar_split_clause,[],[f254,f168,f201,f198,f195,f192,f260,f186])).

fof(f168,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f254,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | spl7_9 ),
    inference(resolution,[],[f169,f84])).

fof(f169,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f253,plain,(
    spl7_18 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl7_18 ),
    inference(resolution,[],[f230,f58])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_18 ),
    inference(resolution,[],[f202,f62])).

fof(f202,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f241,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl7_14 ),
    inference(resolution,[],[f223,f105])).

fof(f105,plain,(
    l1_pre_topc(sK3) ),
    inference(global_subsumption,[],[f61,f103])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f63,f52])).

fof(f223,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_14 ),
    inference(resolution,[],[f190,f62])).

fof(f190,plain,
    ( ~ l1_struct_0(sK3)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f239,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl7_13 ),
    inference(resolution,[],[f220,f61])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_13 ),
    inference(resolution,[],[f187,f62])).

fof(f187,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f227,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl7_17 ),
    inference(resolution,[],[f199,f53])).

fof(f199,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f203,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_5 ),
    inference(avatar_split_clause,[],[f180,f156,f201,f198,f195,f192,f189,f186])).

fof(f156,plain,
    ( spl7_5
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f180,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl7_5 ),
    inference(resolution,[],[f157,f84])).

fof(f157,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f156])).

fof(f179,plain,
    ( ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_2 ),
    inference(avatar_split_clause,[],[f154,f93,f177,f174,f171,f168,f165,f162,f159,f156])).

fof(f154,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(resolution,[],[f33,f100])).

fof(f100,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X3,X2,X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f98,f93,f90])).

fof(f98,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f88,f96,f97,f42])).

fof(f42,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,(
    v1_funct_1(sK2) ),
    inference(global_subsumption,[],[f53])).

fof(f96,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(global_subsumption,[],[f55])).

fof(f95,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f45,f93,f90])).

fof(f45,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (30357)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (30349)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.48  % (30349)Refutation not found, incomplete strategy% (30349)------------------------------
% 0.21/0.48  % (30349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30349)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30349)Memory used [KB]: 10746
% 0.21/0.48  % (30349)Time elapsed: 0.070 s
% 0.21/0.48  % (30349)------------------------------
% 0.21/0.48  % (30349)------------------------------
% 0.21/0.49  % (30347)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (30369)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (30371)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (30357)Refutation not found, incomplete strategy% (30357)------------------------------
% 0.21/0.50  % (30357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30357)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30357)Memory used [KB]: 11129
% 0.21/0.50  % (30357)Time elapsed: 0.089 s
% 0.21/0.50  % (30357)------------------------------
% 0.21/0.50  % (30357)------------------------------
% 0.21/0.50  % (30346)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (30367)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (30350)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (30353)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (30355)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (30353)Refutation not found, incomplete strategy% (30353)------------------------------
% 0.21/0.51  % (30353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30353)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30353)Memory used [KB]: 6268
% 0.21/0.51  % (30353)Time elapsed: 0.101 s
% 0.21/0.51  % (30353)------------------------------
% 0.21/0.51  % (30353)------------------------------
% 0.21/0.51  % (30361)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (30370)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (30368)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (30351)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (30356)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (30366)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (30362)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (30372)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (30348)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  % (30358)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.53  % (30364)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (30359)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.54  % (30372)Refutation not found, incomplete strategy% (30372)------------------------------
% 0.21/0.54  % (30372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30372)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30372)Memory used [KB]: 10746
% 0.21/0.54  % (30372)Time elapsed: 0.138 s
% 0.21/0.54  % (30372)------------------------------
% 0.21/0.54  % (30372)------------------------------
% 0.21/0.54  % (30365)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.54  % (30352)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.58/0.56  % (30355)Refutation not found, incomplete strategy% (30355)------------------------------
% 1.58/0.56  % (30355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (30355)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (30355)Memory used [KB]: 11385
% 1.58/0.56  % (30355)Time elapsed: 0.159 s
% 1.58/0.56  % (30355)------------------------------
% 1.58/0.56  % (30355)------------------------------
% 1.69/0.59  % (30347)Refutation not found, incomplete strategy% (30347)------------------------------
% 1.69/0.59  % (30347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (30347)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (30347)Memory used [KB]: 6396
% 1.69/0.59  % (30347)Time elapsed: 0.149 s
% 1.69/0.59  % (30347)------------------------------
% 1.69/0.59  % (30347)------------------------------
% 1.69/0.59  % (30365)Refutation not found, incomplete strategy% (30365)------------------------------
% 1.69/0.59  % (30365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (30365)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (30365)Memory used [KB]: 2302
% 1.69/0.59  % (30365)Time elapsed: 0.187 s
% 1.69/0.59  % (30365)------------------------------
% 1.69/0.59  % (30365)------------------------------
% 1.69/0.61  % (30371)Refutation not found, incomplete strategy% (30371)------------------------------
% 1.69/0.61  % (30371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (30371)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (30371)Memory used [KB]: 1791
% 1.69/0.61  % (30371)Time elapsed: 0.199 s
% 1.69/0.61  % (30371)------------------------------
% 1.69/0.61  % (30371)------------------------------
% 2.18/0.63  % (30359)Refutation found. Thanks to Tanya!
% 2.18/0.63  % SZS status Theorem for theBenchmark
% 2.18/0.63  % SZS output start Proof for theBenchmark
% 2.18/0.63  fof(f1193,plain,(
% 2.18/0.63    $false),
% 2.18/0.63    inference(avatar_sat_refutation,[],[f95,f101,f179,f203,f227,f239,f241,f253,f262,f269,f280,f287,f294,f301,f303,f602,f664,f693,f821,f841,f904,f921,f923,f925,f998,f1025,f1027,f1029,f1079,f1156,f1188])).
% 2.18/0.63  fof(f1188,plain,(
% 2.18/0.63    ~spl7_2 | ~spl7_59),
% 2.18/0.63    inference(avatar_contradiction_clause,[],[f1187])).
% 2.18/0.63  fof(f1187,plain,(
% 2.18/0.63    $false | (~spl7_2 | ~spl7_59)),
% 2.18/0.63    inference(resolution,[],[f986,f94])).
% 2.18/0.63  fof(f94,plain,(
% 2.18/0.63    sP5(sK4,sK3,sK2,sK1,sK0) | ~spl7_2),
% 2.18/0.63    inference(avatar_component_clause,[],[f93])).
% 2.18/0.63  fof(f93,plain,(
% 2.18/0.63    spl7_2 <=> sP5(sK4,sK3,sK2,sK1,sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.18/0.63  fof(f986,plain,(
% 2.18/0.63    ( ! [X0] : (~sP5(X0,sK3,sK2,sK1,sK0)) ) | ~spl7_59),
% 2.18/0.63    inference(avatar_component_clause,[],[f985])).
% 2.18/0.63  fof(f985,plain,(
% 2.18/0.63    spl7_59 <=> ! [X0] : ~sP5(X0,sK3,sK2,sK1,sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 2.18/0.63  fof(f1156,plain,(
% 2.18/0.63    ~spl7_2 | ~spl7_53),
% 2.18/0.63    inference(avatar_contradiction_clause,[],[f1154])).
% 2.18/0.63  fof(f1154,plain,(
% 2.18/0.63    $false | (~spl7_2 | ~spl7_53)),
% 2.18/0.63    inference(resolution,[],[f901,f94])).
% 2.18/0.63  fof(f901,plain,(
% 2.18/0.63    ( ! [X4] : (~sP5(sK4,X4,sK2,sK1,sK0)) ) | ~spl7_53),
% 2.18/0.63    inference(avatar_component_clause,[],[f900])).
% 2.18/0.63  fof(f900,plain,(
% 2.18/0.63    spl7_53 <=> ! [X4] : ~sP5(sK4,X4,sK2,sK1,sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 2.18/0.63  fof(f1079,plain,(
% 2.18/0.63    ~spl7_61 | ~spl7_62 | ~spl7_63 | ~spl7_49 | ~spl7_50 | ~spl7_51 | ~spl7_52 | ~spl7_60 | spl7_26),
% 2.18/0.63    inference(avatar_split_clause,[],[f1070,f600,f988,f896,f892,f888,f884,f1000,f996,f992])).
% 2.18/0.63  fof(f992,plain,(
% 2.18/0.63    spl7_61 <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 2.18/0.63  fof(f996,plain,(
% 2.18/0.63    spl7_62 <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 2.18/0.63  fof(f1000,plain,(
% 2.18/0.63    spl7_63 <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 2.18/0.63  fof(f884,plain,(
% 2.18/0.63    spl7_49 <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 2.18/0.63  fof(f888,plain,(
% 2.18/0.63    spl7_50 <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 2.18/0.63  fof(f892,plain,(
% 2.18/0.63    spl7_51 <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 2.18/0.63  fof(f896,plain,(
% 2.18/0.63    spl7_52 <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 2.18/0.63  fof(f988,plain,(
% 2.18/0.63    spl7_60 <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 2.18/0.63  fof(f600,plain,(
% 2.18/0.63    spl7_26 <=> sP6(sK2,sK4,sK3,sK1,sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.18/0.63  fof(f1070,plain,(
% 2.18/0.63    ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1069,f305])).
% 2.18/0.63  fof(f305,plain,(
% 2.18/0.63    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))),
% 2.18/0.63    inference(resolution,[],[f216,f52])).
% 2.18/0.63  fof(f52,plain,(
% 2.18/0.63    m1_pre_topc(sK3,sK0)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f16,plain,(
% 2.18/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/0.63    inference(flattening,[],[f15])).
% 2.18/0.63  fof(f15,plain,(
% 2.18/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.18/0.63    inference(ennf_transformation,[],[f12])).
% 2.18/0.63  fof(f12,negated_conjecture,(
% 2.18/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.18/0.63    inference(negated_conjecture,[],[f11])).
% 2.18/0.63  fof(f11,conjecture,(
% 2.18/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.18/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).
% 2.18/0.63  fof(f216,plain,(
% 2.18/0.63    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0))) )),
% 2.18/0.63    inference(global_subsumption,[],[f53,f56,f57,f58,f59,f60,f61,f54,f215])).
% 2.18/0.63  fof(f215,plain,(
% 2.18/0.63    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.18/0.63    inference(forward_demodulation,[],[f204,f131])).
% 2.18/0.63  fof(f131,plain,(
% 2.18/0.63    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)) )),
% 2.18/0.63    inference(global_subsumption,[],[f53,f128])).
% 2.18/0.63  fof(f128,plain,(
% 2.18/0.63    ( ! [X0] : (~v1_funct_1(sK2) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)) )),
% 2.18/0.63    inference(resolution,[],[f87,f55])).
% 2.18/0.63  fof(f55,plain,(
% 2.18/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f87,plain,(
% 2.18/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f32])).
% 2.18/0.63  fof(f32,plain,(
% 2.18/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.18/0.63    inference(flattening,[],[f31])).
% 2.18/0.63  fof(f31,plain,(
% 2.18/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.18/0.63    inference(ennf_transformation,[],[f4])).
% 2.18/0.63  fof(f4,axiom,(
% 2.18/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.18/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.18/0.63  fof(f204,plain,(
% 2.18/0.63    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 2.18/0.63    inference(resolution,[],[f78,f55])).
% 2.18/0.63  fof(f78,plain,(
% 2.18/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 2.18/0.63    inference(cnf_transformation,[],[f22])).
% 2.18/0.63  fof(f22,plain,(
% 2.18/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.63    inference(flattening,[],[f21])).
% 2.18/0.63  fof(f21,plain,(
% 2.18/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.63    inference(ennf_transformation,[],[f7])).
% 2.18/0.63  fof(f7,axiom,(
% 2.18/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.18/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.18/0.63  fof(f54,plain,(
% 2.18/0.63    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f61,plain,(
% 2.18/0.63    l1_pre_topc(sK0)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f60,plain,(
% 2.18/0.63    v2_pre_topc(sK0)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f59,plain,(
% 2.18/0.63    ~v2_struct_0(sK0)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f58,plain,(
% 2.18/0.63    l1_pre_topc(sK1)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f57,plain,(
% 2.18/0.63    v2_pre_topc(sK1)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f56,plain,(
% 2.18/0.63    ~v2_struct_0(sK1)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f53,plain,(
% 2.18/0.63    v1_funct_1(sK2)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f1069,plain,(
% 2.18/0.63    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1068,f304])).
% 2.18/0.63  fof(f304,plain,(
% 2.18/0.63    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))),
% 2.18/0.63    inference(resolution,[],[f216,f48])).
% 2.18/0.63  fof(f48,plain,(
% 2.18/0.63    m1_pre_topc(sK4,sK0)),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f1068,plain,(
% 2.18/0.63    ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1067,f304])).
% 2.18/0.63  fof(f1067,plain,(
% 2.18/0.63    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1066,f304])).
% 2.18/0.63  fof(f1066,plain,(
% 2.18/0.63    ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1065,f304])).
% 2.18/0.63  fof(f1065,plain,(
% 2.18/0.63    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1064,f305])).
% 2.18/0.63  fof(f1064,plain,(
% 2.18/0.63    ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1063,f305])).
% 2.18/0.63  fof(f1063,plain,(
% 2.18/0.63    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(forward_demodulation,[],[f1062,f305])).
% 2.18/0.63  fof(f1062,plain,(
% 2.18/0.63    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_26),
% 2.18/0.63    inference(resolution,[],[f820,f64])).
% 2.18/0.63  fof(f64,plain,(
% 2.18/0.63    ( ! [X4,X2,X0,X3,X1] : (sP6(X4,X3,X2,X1,X0) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) )),
% 2.18/0.63    inference(cnf_transformation,[],[f20])).
% 2.18/0.63  fof(f20,plain,(
% 2.18/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.63    inference(flattening,[],[f19])).
% 2.18/0.63  fof(f19,plain,(
% 2.18/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.63    inference(ennf_transformation,[],[f10])).
% 2.18/0.63  fof(f10,axiom,(
% 2.18/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 2.18/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).
% 2.18/0.63  fof(f820,plain,(
% 2.18/0.63    ~sP6(sK2,sK4,sK3,sK1,sK0) | spl7_26),
% 2.18/0.63    inference(avatar_component_clause,[],[f600])).
% 2.18/0.63  fof(f1029,plain,(
% 2.18/0.63    ~spl7_13 | ~spl7_14 | ~spl7_18 | spl7_63),
% 2.18/0.63    inference(avatar_split_clause,[],[f1028,f1000,f201,f189,f186])).
% 2.18/0.63  fof(f186,plain,(
% 2.18/0.63    spl7_13 <=> l1_struct_0(sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.18/0.63  fof(f189,plain,(
% 2.18/0.63    spl7_14 <=> l1_struct_0(sK3)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.18/0.63  fof(f201,plain,(
% 2.18/0.63    spl7_18 <=> l1_struct_0(sK1)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.18/0.63  fof(f1028,plain,(
% 2.18/0.63    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.18/0.63    inference(global_subsumption,[],[f53,f54,f55,f967])).
% 2.18/0.65  fof(f967,plain,(
% 2.18/0.65    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(superposition,[],[f86,f305])).
% 2.18/0.65  fof(f86,plain,(
% 2.18/0.65    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f30])).
% 2.18/0.65  fof(f30,plain,(
% 2.18/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.18/0.65    inference(flattening,[],[f29])).
% 2.18/0.65  fof(f29,plain,(
% 2.18/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.18/0.65    inference(ennf_transformation,[],[f9])).
% 2.18/0.65  fof(f9,axiom,(
% 2.18/0.65    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 2.18/0.65  fof(f1027,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_14 | ~spl7_18 | spl7_61),
% 2.18/0.65    inference(avatar_split_clause,[],[f1026,f992,f201,f189,f186])).
% 2.18/0.65  fof(f1026,plain,(
% 2.18/0.65    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(global_subsumption,[],[f53,f54,f55,f966])).
% 2.18/0.65  fof(f966,plain,(
% 2.18/0.65    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(superposition,[],[f85,f305])).
% 2.18/0.65  fof(f85,plain,(
% 2.18/0.65    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f30])).
% 2.18/0.65  fof(f1025,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_14 | ~spl7_18 | spl7_60),
% 2.18/0.65    inference(avatar_split_clause,[],[f1024,f988,f201,f189,f186])).
% 2.18/0.65  fof(f1024,plain,(
% 2.18/0.65    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(global_subsumption,[],[f53,f54,f55,f965])).
% 2.18/0.65  fof(f965,plain,(
% 2.18/0.65    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(superposition,[],[f84,f305])).
% 2.18/0.65  fof(f84,plain,(
% 2.18/0.65    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f30])).
% 2.18/0.65  fof(f998,plain,(
% 2.18/0.65    spl7_59 | spl7_62),
% 2.18/0.65    inference(avatar_split_clause,[],[f951,f996,f985])).
% 2.18/0.65  fof(f951,plain,(
% 2.18/0.65    ( ! [X2] : (v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~sP5(X2,sK3,sK2,sK1,sK0)) )),
% 2.18/0.65    inference(superposition,[],[f36,f305])).
% 2.18/0.65  fof(f36,plain,(
% 2.18/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~sP5(X4,X3,X2,X1,X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f925,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_19 | ~spl7_18 | spl7_52),
% 2.18/0.65    inference(avatar_split_clause,[],[f924,f896,f201,f260,f186])).
% 2.18/0.65  fof(f260,plain,(
% 2.18/0.65    spl7_19 <=> l1_struct_0(sK4)),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.18/0.65  fof(f924,plain,(
% 2.18/0.65    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(global_subsumption,[],[f53,f54,f55,f863])).
% 2.18/0.65  fof(f863,plain,(
% 2.18/0.65    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(superposition,[],[f86,f304])).
% 2.18/0.65  fof(f923,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_19 | ~spl7_18 | spl7_50),
% 2.18/0.65    inference(avatar_split_clause,[],[f922,f888,f201,f260,f186])).
% 2.18/0.65  fof(f922,plain,(
% 2.18/0.65    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(global_subsumption,[],[f53,f54,f55,f862])).
% 2.18/0.65  fof(f862,plain,(
% 2.18/0.65    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(superposition,[],[f85,f304])).
% 2.18/0.65  fof(f921,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_19 | ~spl7_18 | spl7_49),
% 2.18/0.65    inference(avatar_split_clause,[],[f920,f884,f201,f260,f186])).
% 2.18/0.65  fof(f920,plain,(
% 2.18/0.65    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(global_subsumption,[],[f53,f54,f55,f861])).
% 2.18/0.65  fof(f861,plain,(
% 2.18/0.65    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.18/0.65    inference(superposition,[],[f84,f304])).
% 2.18/0.65  fof(f904,plain,(
% 2.18/0.65    spl7_53 | spl7_51),
% 2.18/0.65    inference(avatar_split_clause,[],[f851,f892,f900])).
% 2.18/0.65  fof(f851,plain,(
% 2.18/0.65    ( ! [X6] : (v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~sP5(sK4,X6,sK2,sK1,sK0)) )),
% 2.18/0.65    inference(superposition,[],[f40,f304])).
% 2.18/0.65  fof(f40,plain,(
% 2.18/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~sP5(X4,X3,X2,X1,X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f841,plain,(
% 2.18/0.65    spl7_15),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f840])).
% 2.18/0.65  fof(f840,plain,(
% 2.18/0.65    $false | spl7_15),
% 2.18/0.65    inference(resolution,[],[f193,f55])).
% 2.18/0.65  fof(f193,plain,(
% 2.18/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl7_15),
% 2.18/0.65    inference(avatar_component_clause,[],[f192])).
% 2.18/0.65  fof(f192,plain,(
% 2.18/0.65    spl7_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.18/0.65  fof(f821,plain,(
% 2.18/0.65    ~spl7_26 | spl7_1),
% 2.18/0.65    inference(avatar_split_clause,[],[f819,f90,f600])).
% 2.18/0.65  fof(f90,plain,(
% 2.18/0.65    spl7_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.18/0.65  fof(f819,plain,(
% 2.18/0.65    v5_pre_topc(sK2,sK0,sK1) | ~sP6(sK2,sK4,sK3,sK1,sK0)),
% 2.18/0.65    inference(global_subsumption,[],[f53,f56,f57,f58,f54,f55,f556])).
% 2.18/0.65  fof(f556,plain,(
% 2.18/0.65    v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~sP6(sK2,sK4,sK3,sK1,sK0)),
% 2.18/0.65    inference(superposition,[],[f225,f308])).
% 2.18/0.65  fof(f308,plain,(
% 2.18/0.65    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)),
% 2.18/0.65    inference(forward_demodulation,[],[f306,f113])).
% 2.18/0.65  fof(f113,plain,(
% 2.18/0.65    sK2 = k7_relat_1(sK2,u1_struct_0(sK0))),
% 2.18/0.65    inference(global_subsumption,[],[f106,f112])).
% 2.18/0.65  fof(f112,plain,(
% 2.18/0.65    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,u1_struct_0(sK0))),
% 2.18/0.65    inference(resolution,[],[f79,f109])).
% 2.18/0.65  fof(f109,plain,(
% 2.18/0.65    v4_relat_1(sK2,u1_struct_0(sK0))),
% 2.18/0.65    inference(resolution,[],[f81,f55])).
% 2.18/0.65  fof(f81,plain,(
% 2.18/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f26])).
% 2.18/0.65  fof(f26,plain,(
% 2.18/0.65    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.65    inference(ennf_transformation,[],[f14])).
% 2.18/0.65  fof(f14,plain,(
% 2.18/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.18/0.65    inference(pure_predicate_removal,[],[f3])).
% 2.18/0.65  fof(f3,axiom,(
% 2.18/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.18/0.65  fof(f79,plain,(
% 2.18/0.65    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 2.18/0.65    inference(cnf_transformation,[],[f24])).
% 2.18/0.65  fof(f24,plain,(
% 2.18/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/0.65    inference(flattening,[],[f23])).
% 2.18/0.65  fof(f23,plain,(
% 2.18/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/0.65    inference(ennf_transformation,[],[f1])).
% 2.18/0.65  fof(f1,axiom,(
% 2.18/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 2.18/0.65  fof(f106,plain,(
% 2.18/0.65    v1_relat_1(sK2)),
% 2.18/0.65    inference(resolution,[],[f80,f55])).
% 2.18/0.65  fof(f80,plain,(
% 2.18/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f25])).
% 2.18/0.65  fof(f25,plain,(
% 2.18/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.65    inference(ennf_transformation,[],[f2])).
% 2.18/0.65  fof(f2,axiom,(
% 2.18/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.18/0.65  fof(f306,plain,(
% 2.18/0.65    k7_relat_1(sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0)),
% 2.18/0.65    inference(resolution,[],[f216,f144])).
% 2.18/0.65  fof(f144,plain,(
% 2.18/0.65    m1_pre_topc(sK0,sK0)),
% 2.18/0.65    inference(global_subsumption,[],[f47,f51,f59,f61,f48,f52,f142])).
% 2.18/0.65  fof(f142,plain,(
% 2.18/0.65    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 2.18/0.65    inference(superposition,[],[f83,f49])).
% 2.18/0.65  fof(f49,plain,(
% 2.18/0.65    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f83,plain,(
% 2.18/0.65    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f28])).
% 2.18/0.65  fof(f28,plain,(
% 2.18/0.65    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.65    inference(flattening,[],[f27])).
% 2.18/0.65  fof(f27,plain,(
% 2.18/0.65    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.65    inference(ennf_transformation,[],[f13])).
% 2.18/0.65  fof(f13,plain,(
% 2.18/0.65    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.18/0.65    inference(pure_predicate_removal,[],[f8])).
% 2.18/0.65  fof(f8,axiom,(
% 2.18/0.65    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 2.18/0.65  fof(f51,plain,(
% 2.18/0.65    ~v2_struct_0(sK3)),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f47,plain,(
% 2.18/0.65    ~v2_struct_0(sK4)),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f225,plain,(
% 2.18/0.65    ( ! [X0,X1] : (v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~sP6(X1,sK4,sK3,X0,sK0)) )),
% 2.18/0.65    inference(global_subsumption,[],[f47,f51,f59,f60,f61,f48,f52,f50,f224])).
% 2.18/0.65  fof(f224,plain,(
% 2.18/0.65    ( ! [X0,X1] : (v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~sP6(X1,sK4,sK3,X0,sK0) | v2_struct_0(sK0)) )),
% 2.18/0.65    inference(superposition,[],[f76,f49])).
% 2.18/0.65  fof(f76,plain,(
% 2.18/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~sP6(X4,X3,X2,X1,X0) | v2_struct_0(X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f20])).
% 2.18/0.65  fof(f50,plain,(
% 2.18/0.65    r4_tsep_1(sK0,sK3,sK4)),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f693,plain,(
% 2.18/0.65    spl7_11 | ~spl7_26),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f691])).
% 2.18/0.65  fof(f691,plain,(
% 2.18/0.65    $false | (spl7_11 | ~spl7_26)),
% 2.18/0.65    inference(resolution,[],[f271,f601])).
% 2.18/0.65  fof(f601,plain,(
% 2.18/0.65    sP6(sK2,sK4,sK3,sK1,sK0) | ~spl7_26),
% 2.18/0.65    inference(avatar_component_clause,[],[f600])).
% 2.18/0.65  fof(f271,plain,(
% 2.18/0.65    ( ! [X1] : (~sP6(sK2,X1,sK3,sK1,sK0)) ) | spl7_11),
% 2.18/0.65    inference(resolution,[],[f175,f67])).
% 2.18/0.65  fof(f67,plain,(
% 2.18/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~sP6(X4,X3,X2,X1,X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f20])).
% 2.18/0.65  fof(f175,plain,(
% 2.18/0.65    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | spl7_11),
% 2.18/0.65    inference(avatar_component_clause,[],[f174])).
% 2.18/0.65  fof(f174,plain,(
% 2.18/0.65    spl7_11 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.18/0.65  fof(f664,plain,(
% 2.18/0.65    spl7_7 | ~spl7_26),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f662])).
% 2.18/0.65  fof(f662,plain,(
% 2.18/0.65    $false | (spl7_7 | ~spl7_26)),
% 2.18/0.65    inference(resolution,[],[f264,f601])).
% 2.18/0.65  fof(f264,plain,(
% 2.18/0.65    ( ! [X0] : (~sP6(sK2,sK4,X0,sK1,sK0)) ) | spl7_7),
% 2.18/0.65    inference(resolution,[],[f163,f71])).
% 2.18/0.65  fof(f71,plain,(
% 2.18/0.65    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~sP6(X4,X3,X2,X1,X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f20])).
% 2.18/0.65  fof(f163,plain,(
% 2.18/0.65    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | spl7_7),
% 2.18/0.65    inference(avatar_component_clause,[],[f162])).
% 2.18/0.65  fof(f162,plain,(
% 2.18/0.65    spl7_7 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.18/0.65  fof(f602,plain,(
% 2.18/0.65    ~spl7_1 | spl7_26),
% 2.18/0.65    inference(avatar_split_clause,[],[f598,f600,f90])).
% 2.18/0.65  fof(f598,plain,(
% 2.18/0.65    sP6(sK2,sK4,sK3,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.18/0.65    inference(global_subsumption,[],[f53,f56,f57,f58,f54,f55,f597])).
% 2.18/0.65  fof(f597,plain,(
% 2.18/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | sP6(sK2,sK4,sK3,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.18/0.65    inference(duplicate_literal_removal,[],[f553])).
% 2.18/0.65  fof(f553,plain,(
% 2.18/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sP6(sK2,sK4,sK3,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.18/0.65    inference(superposition,[],[f251,f308])).
% 2.18/0.65  fof(f251,plain,(
% 2.18/0.65    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | sP6(X1,sK4,sK3,X0,sK0) | ~v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0)) | ~v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)) )),
% 2.18/0.65    inference(global_subsumption,[],[f47,f51,f59,f60,f61,f48,f52,f50,f248])).
% 2.18/0.65  fof(f248,plain,(
% 2.18/0.65    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | sP6(X1,sK4,sK3,X0,sK0) | ~v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0)) | ~v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | v2_struct_0(sK0)) )),
% 2.18/0.65    inference(superposition,[],[f73,f49])).
% 2.18/0.65  fof(f73,plain,(
% 2.18/0.65    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP6(X4,X3,X2,X1,X0) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f20])).
% 2.18/0.65  fof(f303,plain,(
% 2.18/0.65    spl7_16),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f302])).
% 2.18/0.65  fof(f302,plain,(
% 2.18/0.65    $false | spl7_16),
% 2.18/0.65    inference(resolution,[],[f196,f54])).
% 2.18/0.65  fof(f196,plain,(
% 2.18/0.65    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl7_16),
% 2.18/0.65    inference(avatar_component_clause,[],[f195])).
% 2.18/0.65  fof(f195,plain,(
% 2.18/0.65    spl7_16 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.18/0.65  fof(f301,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_10),
% 2.18/0.65    inference(avatar_split_clause,[],[f296,f171,f201,f198,f195,f192,f189,f186])).
% 2.18/0.65  fof(f198,plain,(
% 2.18/0.65    spl7_17 <=> v1_funct_1(sK2)),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.18/0.65  fof(f171,plain,(
% 2.18/0.65    spl7_10 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.18/0.65  fof(f296,plain,(
% 2.18/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl7_10),
% 2.18/0.65    inference(resolution,[],[f172,f86])).
% 2.18/0.65  fof(f172,plain,(
% 2.18/0.65    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl7_10),
% 2.18/0.65    inference(avatar_component_clause,[],[f171])).
% 2.18/0.65  fof(f294,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_19 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_6),
% 2.18/0.65    inference(avatar_split_clause,[],[f289,f159,f201,f198,f195,f192,f260,f186])).
% 2.18/0.65  fof(f159,plain,(
% 2.18/0.65    spl7_6 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.18/0.65  fof(f289,plain,(
% 2.18/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0) | spl7_6),
% 2.18/0.65    inference(resolution,[],[f160,f86])).
% 2.18/0.65  fof(f160,plain,(
% 2.18/0.65    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | spl7_6),
% 2.18/0.65    inference(avatar_component_clause,[],[f159])).
% 2.18/0.65  fof(f287,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_12),
% 2.18/0.65    inference(avatar_split_clause,[],[f282,f177,f201,f198,f195,f192,f189,f186])).
% 2.18/0.65  fof(f177,plain,(
% 2.18/0.65    spl7_12 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.18/0.65  fof(f282,plain,(
% 2.18/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl7_12),
% 2.18/0.65    inference(resolution,[],[f178,f85])).
% 2.18/0.65  fof(f178,plain,(
% 2.18/0.65    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_12),
% 2.18/0.65    inference(avatar_component_clause,[],[f177])).
% 2.18/0.65  fof(f280,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_19 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_8),
% 2.18/0.65    inference(avatar_split_clause,[],[f275,f165,f201,f198,f195,f192,f260,f186])).
% 2.18/0.65  fof(f165,plain,(
% 2.18/0.65    spl7_8 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.18/0.65  fof(f275,plain,(
% 2.18/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0) | spl7_8),
% 2.18/0.65    inference(resolution,[],[f166,f85])).
% 2.18/0.65  fof(f166,plain,(
% 2.18/0.65    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | spl7_8),
% 2.18/0.65    inference(avatar_component_clause,[],[f165])).
% 2.18/0.65  fof(f269,plain,(
% 2.18/0.65    spl7_19),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f268])).
% 2.18/0.65  fof(f268,plain,(
% 2.18/0.65    $false | spl7_19),
% 2.18/0.65    inference(resolution,[],[f263,f104])).
% 2.18/0.65  fof(f104,plain,(
% 2.18/0.65    l1_pre_topc(sK4)),
% 2.18/0.65    inference(global_subsumption,[],[f61,f102])).
% 2.18/0.65  fof(f102,plain,(
% 2.18/0.65    ~l1_pre_topc(sK0) | l1_pre_topc(sK4)),
% 2.18/0.65    inference(resolution,[],[f63,f48])).
% 2.18/0.65  fof(f63,plain,(
% 2.18/0.65    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f18])).
% 2.18/0.65  fof(f18,plain,(
% 2.18/0.65    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/0.65    inference(ennf_transformation,[],[f6])).
% 2.18/0.65  fof(f6,axiom,(
% 2.18/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.18/0.65  fof(f263,plain,(
% 2.18/0.65    ~l1_pre_topc(sK4) | spl7_19),
% 2.18/0.65    inference(resolution,[],[f261,f62])).
% 2.18/0.65  fof(f62,plain,(
% 2.18/0.65    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.18/0.65    inference(cnf_transformation,[],[f17])).
% 2.18/0.65  fof(f17,plain,(
% 2.18/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.18/0.65    inference(ennf_transformation,[],[f5])).
% 2.18/0.65  fof(f5,axiom,(
% 2.18/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.18/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.18/0.65  fof(f261,plain,(
% 2.18/0.65    ~l1_struct_0(sK4) | spl7_19),
% 2.18/0.65    inference(avatar_component_clause,[],[f260])).
% 2.18/0.65  fof(f262,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_19 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_9),
% 2.18/0.65    inference(avatar_split_clause,[],[f254,f168,f201,f198,f195,f192,f260,f186])).
% 2.18/0.65  fof(f168,plain,(
% 2.18/0.65    spl7_9 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.18/0.65  fof(f254,plain,(
% 2.18/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0) | spl7_9),
% 2.18/0.65    inference(resolution,[],[f169,f84])).
% 2.18/0.65  fof(f169,plain,(
% 2.18/0.65    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | spl7_9),
% 2.18/0.65    inference(avatar_component_clause,[],[f168])).
% 2.18/0.65  fof(f253,plain,(
% 2.18/0.65    spl7_18),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f252])).
% 2.18/0.65  fof(f252,plain,(
% 2.18/0.65    $false | spl7_18),
% 2.18/0.65    inference(resolution,[],[f230,f58])).
% 2.18/0.65  fof(f230,plain,(
% 2.18/0.65    ~l1_pre_topc(sK1) | spl7_18),
% 2.18/0.65    inference(resolution,[],[f202,f62])).
% 2.18/0.65  fof(f202,plain,(
% 2.18/0.65    ~l1_struct_0(sK1) | spl7_18),
% 2.18/0.65    inference(avatar_component_clause,[],[f201])).
% 2.18/0.65  fof(f241,plain,(
% 2.18/0.65    spl7_14),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f240])).
% 2.18/0.65  fof(f240,plain,(
% 2.18/0.65    $false | spl7_14),
% 2.18/0.65    inference(resolution,[],[f223,f105])).
% 2.18/0.65  fof(f105,plain,(
% 2.18/0.65    l1_pre_topc(sK3)),
% 2.18/0.65    inference(global_subsumption,[],[f61,f103])).
% 2.18/0.65  fof(f103,plain,(
% 2.18/0.65    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 2.18/0.65    inference(resolution,[],[f63,f52])).
% 2.18/0.65  fof(f223,plain,(
% 2.18/0.65    ~l1_pre_topc(sK3) | spl7_14),
% 2.18/0.65    inference(resolution,[],[f190,f62])).
% 2.18/0.65  fof(f190,plain,(
% 2.18/0.65    ~l1_struct_0(sK3) | spl7_14),
% 2.18/0.65    inference(avatar_component_clause,[],[f189])).
% 2.18/0.65  fof(f239,plain,(
% 2.18/0.65    spl7_13),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f238])).
% 2.18/0.65  fof(f238,plain,(
% 2.18/0.65    $false | spl7_13),
% 2.18/0.65    inference(resolution,[],[f220,f61])).
% 2.18/0.65  fof(f220,plain,(
% 2.18/0.65    ~l1_pre_topc(sK0) | spl7_13),
% 2.18/0.65    inference(resolution,[],[f187,f62])).
% 2.18/0.65  fof(f187,plain,(
% 2.18/0.65    ~l1_struct_0(sK0) | spl7_13),
% 2.18/0.65    inference(avatar_component_clause,[],[f186])).
% 2.18/0.65  fof(f227,plain,(
% 2.18/0.65    spl7_17),
% 2.18/0.65    inference(avatar_contradiction_clause,[],[f226])).
% 2.18/0.65  fof(f226,plain,(
% 2.18/0.65    $false | spl7_17),
% 2.18/0.65    inference(resolution,[],[f199,f53])).
% 2.18/0.65  fof(f199,plain,(
% 2.18/0.65    ~v1_funct_1(sK2) | spl7_17),
% 2.18/0.65    inference(avatar_component_clause,[],[f198])).
% 2.18/0.65  fof(f203,plain,(
% 2.18/0.65    ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_5),
% 2.18/0.65    inference(avatar_split_clause,[],[f180,f156,f201,f198,f195,f192,f189,f186])).
% 2.18/0.65  fof(f156,plain,(
% 2.18/0.65    spl7_5 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 2.18/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.18/0.65  fof(f180,plain,(
% 2.18/0.65    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl7_5),
% 2.18/0.65    inference(resolution,[],[f157,f84])).
% 2.18/0.65  fof(f157,plain,(
% 2.18/0.65    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_5),
% 2.18/0.65    inference(avatar_component_clause,[],[f156])).
% 2.18/0.65  fof(f179,plain,(
% 2.18/0.65    ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_2),
% 2.18/0.65    inference(avatar_split_clause,[],[f154,f93,f177,f174,f171,f168,f165,f162,f159,f156])).
% 2.18/0.65  fof(f154,plain,(
% 2.18/0.65    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.18/0.65    inference(resolution,[],[f33,f100])).
% 2.18/0.65  fof(f100,plain,(
% 2.18/0.65    ~sP5(sK4,sK3,sK2,sK1,sK0) | spl7_2),
% 2.18/0.65    inference(avatar_component_clause,[],[f93])).
% 2.18/0.65  fof(f33,plain,(
% 2.18/0.65    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X3,X2,X1,X0) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f101,plain,(
% 2.18/0.65    ~spl7_1 | ~spl7_2),
% 2.18/0.65    inference(avatar_split_clause,[],[f98,f93,f90])).
% 2.18/0.65  fof(f98,plain,(
% 2.18/0.65    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.18/0.65    inference(global_subsumption,[],[f88,f96,f97,f42])).
% 2.18/0.65  fof(f42,plain,(
% 2.18/0.65    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  fof(f97,plain,(
% 2.18/0.65    v1_funct_1(sK2)),
% 2.18/0.65    inference(global_subsumption,[],[f53])).
% 2.18/0.65  fof(f96,plain,(
% 2.18/0.65    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.18/0.65    inference(global_subsumption,[],[f54])).
% 2.18/0.65  fof(f88,plain,(
% 2.18/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.18/0.65    inference(global_subsumption,[],[f55])).
% 2.18/0.65  fof(f95,plain,(
% 2.18/0.65    spl7_1 | spl7_2),
% 2.18/0.65    inference(avatar_split_clause,[],[f45,f93,f90])).
% 2.18/0.65  fof(f45,plain,(
% 2.18/0.65    sP5(sK4,sK3,sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 2.18/0.65    inference(cnf_transformation,[],[f16])).
% 2.18/0.65  % SZS output end Proof for theBenchmark
% 2.18/0.65  % (30359)------------------------------
% 2.18/0.65  % (30359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.65  % (30359)Termination reason: Refutation
% 2.18/0.65  
% 2.18/0.65  % (30359)Memory used [KB]: 12537
% 2.18/0.65  % (30359)Time elapsed: 0.242 s
% 2.18/0.65  % (30359)------------------------------
% 2.18/0.65  % (30359)------------------------------
% 2.35/0.66  % (30342)Success in time 0.3 s
%------------------------------------------------------------------------------
